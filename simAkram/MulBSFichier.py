#!/usr/bin/env python2
# -*- coding: utf-8 -*-
"""
 LoRaSim 0.2.1: simulate collisions in LoRa - multiple base stations variant
 Copyright © 2016-2017 Thiemo Voigt <thiemo@sics.se> and Martin Bor <m.bor@lancaster.ac.uk>

 This work is licensed under the Creative Commons Attribution 4.0
 International License. To view a copy of this license,
 visit http://creativecommons.org/licenses/by/4.0/.

 Do LoRa Low-Power Wide-Area Networks Scale? Martin Bor, Utz Roedig, Thiemo Voigt
 and Juan Alonso, MSWiM '16, http://dx.doi.org/10.1145/2988287.2989163

 $Date: 2017-05-12 19:16:16 +0100 (Fri, 12 May 2017) $
 $Revision: 334 $
"""

"""
 SYNOPSIS:
   ./loraDirMulBS.py <nodes> <avgsend> <experiment> <simtime> <basestation> [collision]
 DESCRIPTION:
    nodes
        number of nodes to simulate
    avgsend
        average sending interval in milliseconds
    experiment
        experiment is an integer that determines with what radio settings the
        simulation is run. All nodes are configured with a fixed transmit power
        and a single transmit frequency, unless stated otherwise.
        0   use the settings with the the slowest datarate (SF12, BW125, CR4/8).
        1   similair to experiment 0, but use a random choice of 3 transmit
            frequencies.
        2   use the settings with the fastest data rate (SF6, BW500, CR4/5).
        3   optimise the setting per node based on the distance to the gateway.
        4   use the settings as defined in LoRaWAN (SF12, BW125, CR4/5).
        5   similair to experiment 3, but also optimises the transmit power.
    simtime
        total running time in milliseconds
    basestation
        number of base stations to simulate. Can be either 1, 2, 3, 4, 6, 8 or 24.
    collision
        set to 1 to enable the full collision check, 0 to use a simplified check.
        With the simplified check, two messages collide when they arrive at the
        same time, on the same frequency and spreading factor. The full collision
        check considers the 'capture effect', whereby a collision of one or the
 OUTPUT
    The result of every simulation run will be appended to a file named expX.dat,
    whereby X is the experiment number. The file contains a space separated table
    of values for nodes, collisions, transmissions and total energy spent. The
    data file can be easily plotted using e.g. gnuplot.
"""

import simpy
import random
import numpy as np
import math
import sys
import re
import matplotlib.pyplot as plt
import os
import operator
import scipy
import scipy.stats
from matplotlib.patches import Rectangle

# turn on/off graphics
graphics = 1

# this is an array with measured values for sensitivity
# see paper, Table 3
#sf7 = np.array([7,-126.5,-124.25,-120.75])
#sf8 = np.array([8,-127.25,-126.75,-124.0])
#sf9 = np.array([9,-131.25,-128.25,-127.5])
#sf10 = np.array([10,-132.75,-130.25,-128.75])
#sf11 = np.array([11,-134.5,-132.75,-130])
#sf12 = np.array([12,-133.25,-132.25,-132.25])
sf7 = np.array([7,-123,-120,-117.0])
sf8 = np.array([8,-126,-123,-120.0])
sf9 = np.array([9,-129,-126,-123.0])
sf10 = np.array([10,-132,-129,-126.0])
sf11 = np.array([11,-134.53,-131.52,-128.51])
sf12 = np.array([12,-137,-134,-131.0])

sensi = np.array([sf7,sf8,sf9,sf10,sf11,sf12])

IS7 = np.array([1,-8,-9,-9,-9,-9])
IS8 = np.array([-11,1,-11,-12,-13,-13])
IS9 = np.array([-15,-13,1,-13,-14,-15])
IS10 = np.array([-19,-18,-17,1,-17,-18])
IS11 = np.array([-22,-22,-21,-20,1,-20])
IS12 = np.array([-25,-25,-25,-24,-23,1])
IsoThresholds = np.array([IS7,IS8,IS9,IS10,IS11,IS12])

# Bandwidth
Bandwidth = 500
# Coding Rate
CodingRate = 1
# packet size per SFs
PcktLength_SF = [20,20,20,20,20,20]
LorawanHeader = 7
# last time the gateway acked a package
nearstACK1p = [0,0,0] # 3 channels with 1% duty cycle
nearstACK10p = 0 # one channel with 10% duty cycle
AckMessLen = 0

#
# packet error model assumming independent Bernoulli
#
from scipy.stats import norm
def ber_reynders(eb_no, sf):
    """Given the energy per bit to noise ratio (in db), compute the bit error for the SF"""
    return norm.sf(math.log(sf, 12)/math.sqrt(2)*eb_no)

def ber_reynders_snr(snr, sf, bw, cr):
    """Compute the bit error given the SNR (db) and SF"""
    Temp = [4.0/5,4.0/6,4.0/7,4.0/8]
    CR = Temp[cr-1]
    BW = bw*1000.0
    eb_no =  snr - 10*math.log10(BW/2**sf) - 10*math.log10(sf) - 10*math.log10(CR) + 10*math.log10(BW)
    return ber_reynders(eb_no, sf)

def per(sf,bw,cr,rssi,pl):
    snr = rssi  +174 - 10*math.log10(bw) - 6
    return 1 - (1 - ber_reynders_snr(snr, sf, bw, cr))**(pl*8)



def checkACK(packet):
    global  nearstACK1p
    global  nearstACK10p
    # check ack in the first window
    chanlindex=[872000000, 864000000, 860000000, 868000000].index(packet.freq)
    timeofacking = env.now + 1  # one sec after receiving the packet
    if (timeofacking >= nearstACK1p[chanlindex]):
        # this packet can be acked
        packet.acked = 1
        tempairtime = airtime(packet.sf, CodingRate, AckMessLen+LorawanHeader, Bandwidth)
        nearstACK1p[chanlindex] = timeofacking+(tempairtime/0.01)
        nodes[packet.nodeid].rxtime += tempairtime
        return packet.acked
    else:
        # this packet can not be acked
        packet.acked = 0
        Tsym = (2**packet.sf)/(Bandwidth*1000) # sec
        Tpream = (8 + 4.25)*Tsym
        nodes[packet.nodeid].rxtime += Tpream

    # chcek ack in the second window
    timeofacking = env.now + 2  # two secs after receiving the packet
    if (timeofacking >= nearstACK10p):
        # this packet can be acked
        packet.acked = 1
        tempairtime = airtime(12, CodingRate, AckMessLen+LorawanHeader, Bandwidth)
        nearstACK10p = timeofacking+(tempairtime/0.1)
        nodes[packet.nodeid].rxtime += tempairtime
        return packet.acked
    else:
        # this packet can not be acked
        packet.acked = 0
        Tsym = (2.0**12)/(Bandwidth*1000.0) # sec
        Tpream = (8 + 4.25)*Tsym
        nodes[packet.nodeid].rxtime += Tpream
        return packet.acked
#
# check for collisions at base station
# Note: called before a packet (or rather node) is inserted into the list
def checkcollision(packet):
    col = 0 # flag needed since there might be several collisions for packet
    # lost packets don't collide
    if packet.lost:
       return 0
    if packetsAtBS[packet.bs]:
        for other in packetsAtBS[packet.bs]:
            if other.id != packet.nodeid:
	       print ">> node {} (sf:{} bw:{} freq:{:.6e})".format(
               other.nodeid, other.packet[packet.bs].sf, other.packet[packet.bs].bw, other.packet[packet.bs].freq)
               if(full_collision == 1 or full_collision == 2):
                   if frequencyCollision(packet, other.packet[packet.bs]) \
                   and timingCollision(packet, other.packet[packet.bs]):
                       # check who collides in the power domain
                       if (full_collision == 1):
                          # Capture effect
                          c = powerCollision_1(packet, other.packet[packet.bs])
                       else:
                          # Capture + Non-orthognalitiy SFs effects
                          c = powerCollision_2(packet, other.packet[packet.bs])
                       # mark all the collided packets
                       # either this one, the other one, or both
                       for p in c:
                          p.collided = 1
                          if p == packet:
                             col = 1
                   else:
                       # no freq or timing collision, all fine
                       pass
               else:
                   # simple collision
                   if frequencyCollision(packet, other.packet[packet.bs]) \
                   and sfCollision(packet, other.packet[packet.bs]):
                       packet.collided = 1
                       other.packet[packet.bs].collided = 1  # other also got lost, if it wasn't lost already
                       col = 1
        return col
    return 0

# Note: called before a packet (or rather node) is inserted into the list
#
# frequencyCollision, conditions
#
#        |f1-f2| <= 120 kHz if f1 or f2 has bw 500
#        |f1-f2| <= 60 kHz if f1 or f2 has bw 250
#        |f1-f2| <= 30 kHz if f1 or f2 has bw 125
def frequencyCollision(p1,p2):
    if (abs(p1.freq-p2.freq)<=120 and (p1.bw==500 and p2.bw==500)):
        return True
    elif (abs(p1.freq-p2.freq)<=60 and (p1.bw==250 and p2.bw==250)):
        return True
    else:
        if (abs(p1.freq-p2.freq)<=30):
            return True
    return False

def sfCollision(p1, p2):
    if p1.sf == p2.sf:
        # p2 may have been lost too, will be marked by other checks
        return True
    return False

def powerCollision(p1, p2):
    powerThreshold = 6 # dB
    print "pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2))
    if abs(p1.rssi - p2.rssi) < powerThreshold:
        print "collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid)
        # packets are too close to each other, both collide
        # return both packets as casualties
        return (p1, p2)
    elif p1.rssi - p2.rssi < powerThreshold:
        # p2 overpowered p1, return p1 as casualty
        print "collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid)
        return (p1,)
    print "p1 wins, p2 lost"
    # p2 was the weaker packet, return it as a casualty
    return (p2,)


# check only the capture between the same spreading factor
def powerCollision_1(p1, p2):
    #powerThreshold = 6
    print "pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2))
    if p1.sf == p2.sf:
       if abs(p1.rssi - p2.rssi) < IsoThresholds[p1.sf-7][p2.sf-7]:
            print "collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid)
            # packets are too close to each other, both collide
            # return both pack ets as casualties
            return (p1, p2)
       elif p1.rssi - p2.rssi < IsoThresholds[p1.sf-7][p2.sf-7]:
            # p2 overpowered p1, return p1 as casualty
            print "collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid)
            return (p1,)
       print "p1 wins, p2 lost"
       # p2 was the weaker packet, return it as a casualty
       return (p2,)
    else:
       return ()


# check the capture effect and checking the effect of pesudo-orthognal SFs
def powerCollision_2(p1, p2):
    #powerThreshold = 6
    print "SF: node {0.nodeid} {0.sf} node {1.nodeid} {1.sf}".format(p1, p2)
    print "pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2))
    if p1.sf == p2.sf:
       if abs(p1.rssi - p2.rssi) < IsoThresholds[p1.sf-7][p2.sf-7]:
           print "collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid)
           # packets are too close to each other, both collide
           # return both packets as casualties
           return (p1, p2)
       elif p1.rssi - p2.rssi < IsoThresholds[p1.sf-7][p2.sf-7]:
           # p2 overpowered p1, return p1 as casualty
           print "collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid)
           print "capture - p2 wins, p1 lost"
           return (p1,)
       print "capture - p1 wins, p2 lost"
       # p2 was the weaker packet, return it as a casualty
       return (p2,)
    else:
       if p1.rssi-p2.rssi > IsoThresholds[p1.sf-7][p2.sf-7]:
          print "P1 is OK"
          if p2.rssi-p1.rssi > IsoThresholds[p2.sf-7][p1.sf-7]:
              print "p2 is OK"
              return ()
          else:
              print "p2 is lost"
              return (p2,)
       else:
           print "p1 is lost"
           if p2.rssi-p1.rssi > IsoThresholds[p2.sf-7][p1.sf-7]:
               print "p2 is OK"
               return (p1,)
           else:
               print "p2 is lost"
               return (p1,p2)


def timingCollision(p1, p2):
    # assuming p1 is the freshly arrived packet and this is the last check
    # we've already determined that p1 is a weak packet, so the only
    # way we can win is by being late enough (only the first n - 5 preamble symbols overlap)

    # assuming 8 preamble symbols
    Npream = 8

    # we can lose at most (Npream - 5) * Tsym of our preamble
    Tpreamb = 2**p1.sf/(1.0*p1.bw) * (Npream - 5)

    # check whether p2 ends in p1's critical section
    p2_end = p2.addTime + p2.rectime
    p1_cs = env.now + Tpreamb
    if p1_cs < p2_end:
        # p1 collided with p2 and lost
        return True
    return False

# this function computes the airtime of a packet
# according to LoraDesignGuide_STD.pdf
#
def airtime(sf,cr,pl,bw):
    H = 0        # implicit header disabled (H=0) or not (H=1)
    DE = 0       # low data rate optimization enabled (=1) or not (=0)
    Npream = 8   # number of preamble symbol (12.25  from Utz paper)

    if bw == 125 and sf in [11, 12]:
        # low data rate optimization mandated for BW125 with SF11 and SF12
        DE = 1
    if sf == 6:
        # can only have implicit header with SF6
        H = 1

    Tsym = (2.0**sf)/bw
    Tpream = (Npream + 4.25)*Tsym
    payloadSymbNB = 8 + max(math.ceil((8.0*pl-4.0*sf+28+16-20*H)/(4.0*(sf-2*DE)))*(cr+4),0)
    Tpayload = payloadSymbNB * Tsym
    return Tpream + Tpayload



#
# this function creates a BS
#
class myBS():
    def __init__(self, id, X, Y):
        self.id = id
        self.x = 0
        self.y = 0

        # This is a hack for now
        global nrBS
        global maxDist
        global maxX
        global maxY

        if (nrBS == 1 and self.id == 0):
            self.x = maxX/2.0
            self.y = maxY/2.0


        if (nrBS == 3 or nrBS == 2):
            self.x = (self.id+1)*maxX/float(nrBS+1)
            self.y = maxY/2.0

        if (nrBS == 4):
            if (self.id < 2):
                self.x = (self.id+1)*maxX/3.0
                self.y = maxY/3.0
            else:
                self.x = (self.id+1-2)*maxX/3.0
                self.y = 2*maxY/3.0

        if (nrBS == 6):
            if (self.id < 3):
                self.x = (self.id+1)*maxX/4.0
                self.y = maxY/3.0
            else:
                self.x = (self.id+1-3)*maxX/4.0
                self.y = 2*maxY/3.0

        if (nrBS == 8):
            if (self.id < 4):
                self.x = (self.id+1)*maxX/5.0
                self.y = maxY/3.0
            else:
                self.x = (self.id+1-4)*maxX/5.0
                self.y = 2*maxY/3.0

        if (nrBS == 24):
            if (self.id < 8):
                self.x = (self.id+1)*maxX/9.0
                self.y = maxY/4.0
            elif (self.id < 16):
                self.x = (self.id+1-8)*maxX/9.0
                self.y = 2*maxY/4.0
            else:
                self.x = (self.id+1-16)*maxX/9.0
                self.y = 3*maxY/4.0

        self.x = X
        self.y = Y
        print "BSx:", self.x, "BSy:", self.y                                      

        global graphics
        if (graphics):
          global ax
          ax.add_artist(plt.Circle((self.x, self.y), 15, fill=True, color='blue'))
          ax.add_artist(plt.Circle((self.x, self.y), maxDist, fill=False, color='blue'))


# this function creates a node

class myNode():
    def __init__(self, id,bases, period, packetlen, X,Y):
        global bs

        self.id = id
        self.period = period
        self.x = 0
        self.y = 0
        global bs
        self.nodeid = id
        self.buffer = packetlen
        self.bases = bases
        self.first = 1
        self.lstretans = 0
        self.sent = 0
        self.coll = 0
        self.lost = 0
        self.noack = 0
        self.acklost = 0
        self.recv = 0
        self.losterror = 0
        self.rxtime = 0
        self.packet = []
        self.distances = []
        # this is very complex prodecure for placing nodes
        # and ensure minimum distance between each pair of nodes
        found = 0
        rounds = 0
        global nodes
        while (found == 0 and rounds < 100):
            global maxX
            global maxY
            posx = random.randint(0,int(maxX))
            posy = random.randint(0,int(maxY))
            if len(nodes) > 0:
                for index, n in enumerate(nodes):
                    dist = np.sqrt(((abs(n.x-posx))**2)+((abs(n.y-posy))**2))
                    if dist >= 10:
                        found = 1
                        self.x = posx
                        self.y = posy
                    else:
                        rounds = rounds + 1
                        if rounds == 100:
                            print "could not place new node, giving up"
                            exit(-2)
            else:
                print "first node"
                self.x = posx
                self.y = posy
                found = 1
        self.x = X
        self.y = Y
        # create "virtual" packet for each BS
        global nrBS
        for i in range(0,nrBS):
            d = np.sqrt((self.x-bs[i].x)*(self.x-bs[i].x)+(self.y-bs[i].y)*(self.y-bs[i].y))
            self.distances.append(d)
            self.packet.append(myPacket(self.id, packetlen, self.distances[i], i))
        print('node %d' %id, "x", self.x, "y", self.y, "dist: ", self.distances)

        self.sent = 0

        # graphics for node
        global graphics
        if (graphics == 1):
            global ax
            ax.add_artist(plt.Circle((self.x, self.y), 15, fill=True, color='green'))

#
# this function creates a packet (associated with a node)
# it also sets all parameters, currently random
#
class myPacket():
    def __init__(self, nodeid, plen, distance, bs ):
        global experiment
        global Ptx
        global gamma
        global d0
        global var
        global Lpld0
        global GL


        # new: base station ID
        self.bs = bs
        self.nodeid = nodeid
        # randomize configuration values
        self.sf = random.randint(6,12)
        self.cr = random.randint(1,4)
        self.bw = random.choice([125, 250, 500])
        self.txpow = 14
        # for certain experiments override these
        if experiment==1 or experiment == 0:
            self.sf = 12
            self.cr = 4
            self.bw = 125

        # for certain experiments override these
        if experiment==2:
            self.sf = 6
            self.cr = 1
            self.bw = 500
	# paramétrer le facteur d'étalement et la bande passante selon les données utilisées
	if experiment > 5:
	    self.sf = SF
            self.cr = 1
            self.bw = BW


        # for experiment 3 find the best setting
        # OBS, some hardcoded values
        Prx = Ptx  ## zero path loss by default

        # log-shadow
        Lpl = Lpld0 + 10*gamma*math.log10(distance/d0)
        print Lpl
        Prx = Ptx - GL - Lpl

        if (experiment == 3):
            minairtime = 9999
            minsf = 0
            minbw = 0

            for i in range(0,6):
                for j in range(1,4):
                    if (sensi[i,j] < Prx):
                        self.sf = sensi[i,0]
                        if j==1:
                            self.bw = 125
                        elif j==2:
                            self.bw = 250
                        else:
                            self.bw=500
                        at = airtime(self.sf,4,20,self.bw)
                        if at < minairtime:
                            minairtime = at
                            minsf = self.sf
                            minbw = self.bw

            self.rectime = minairtime
            self.sf = minsf
            self.bw = minbw
            if (minairtime == 9999):
                print "does not reach base station"
                exit(-1)

        # transmission range, needs update XXX
        self.transRange = 150
        self.pl = plen
        self.symTime = (2.0**self.sf)/self.bw
        self.arriveTime = 0
        self.rssi = Prx
        # frequencies: lower bound + number of 61 Hz steps
        self.freq = 860000000 + random.randint(0,2622950)

        # for certain experiments override these and
        # choose some random frequences
        if experiment == 1:
            self.freq = random.choice([860000000, 864000000, 868000000])
        else:
            self.freq = 860000000

        self.rectime = airtime(self.sf,self.cr,self.pl,self.bw)
        # denote if packet is collided
        self.collided = 0
        self.processed = 0
	self.lost = False
        self.perror = False
        self.acked = 0
        self.acklost = 0
        # mark the packet as lost when it's rssi is below the sensitivity
        # don't do this for experiment 3, as it requires a bit more work
        if experiment != 3:
            global minsensi
            self.lost = self.rssi < minsensi
            print "node {} bs {} lost {}".format(self.nodeid, self.bs, self.lost)


#
# main discrete event loop, runs for each node
# a global list of packet being processed at the gateway
# is maintained
#
def transmit(env,node):
    while True:
        yield env.timeout(random.expovariate(1.0/float(node.period)))
        # time sending and receiving
        # packet arrives -> add to base station
        node.sent = node.sent + 1
   
        global packetSeq
        packetSeq = packetSeq + 1

        global nrBS
        for bs in range(0, nrBS):    
          if (node in packetsAtBS):
                print "ERROR: packet already in"
          else:
 
            node.packet[bs].rssi = node.packet[bs].txpow - Lpld0 - 10*gamma*math.log10(node.distances[bs]/d0) - np.random.normal(-var, var)
            sensitivity = sensi[node.packet[bs].sf - 7, [125,250,500].index(node.packet[bs].bw) + 1]
            if node.packet[bs].rssi < sensitivity:
                print "node {}: packet will be lost".format(node.nodeid)
                node.packet[bs].lost = True
            else:
                node.packet[bs].lost = False
                if (per(node.packet[bs].sf,node.packet[bs].bw,node.packet[bs].cr,node.packet[bs].rssi,node.packet[bs].pl) < random.uniform(0,1)):
                    # OK CRC
                    node.packet[bs].perror = False
                else:
                    # Bad CRC
                    node.packet[bs].perror = True
                # adding packet if no collision
            if (checkcollision(node.packet[bs])==1):
                    node.packet[bs].collided = 1
      
            else:
                    node.packet[bs].collided = 0
            packetsAtBS[bs].append(node)   
            node.packet[bs].addTime = env.now
            node.packet[bs].seqNr = packetSeq
        yield env.timeout(node.packet[0].rectime)
        for bs in range(0, nrBS):  
          if (node.packet[bs].lost == 0\
             and node.packet[bs].perror == False\
             and node.packet[bs].collided == False\
             and checkACK(node.packet[bs])):
                 node.packet[bs].acked = 1
                 # the packet can be acked
                 # check if the ack is lost or not
                 if((14 - Lpld0 - 10*gamma*math.log10(node.distances[bs]/d0) - np.random.normal(-var, var)) > sensi[node.packet[bs].sf-7, [125,250,500].index(node.packet[bs].bw) + 1]):
                    # the ack is not lost
                    node.packet[bs].acklost = 0
                 else:
                    # ack is lost
                    node.packet[bs].acklost = 1
          else:
                node.packet[bs].acked = 0

         
	  
          if node.packet[bs].processed == 1:
                global nrProcessed
                nrProcessed = nrProcessed + 1
          if node.packet[bs].lost:
                #node.buffer += PcktLength_SF[node.parameters.sf-7]
	        lostPackets.append(node.packet[bs].seqNr)
                print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
                node.lost = node.lost + 1
                node.lstretans += 1
                global nrLost
                nrLost += 1
          if node.packet[bs].perror:
		print "Je suis dans le perror"
                print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
                node.losterror = node.losterror + 1
                global nrLostError
                nrLostError += 1
          if node.packet[bs].collided == 1:
		print "Je suis dans collided"
                #node.buffer += PcktLength_SF[node.parameters.sf-7]
	        collidedPackets.append(node.packet[bs].seqNr)
                print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
                node.coll = node.coll + 1
                node.lstretans += 1
                global nrCollisions
                nrCollisions += 1
          if node.packet[bs].acked == 0:
		print "Je suis dans le ack"
                #node.buffer += PcktLength_SF[node.parameters.sf-7]
                print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
                node.noack = node.noack + 1
                node.lstretans += 1
                global nrNoACK
                nrNoACK += 1
          if node.packet[bs].acklost == 1:
		print "Je suis dans le acklost"
                #node.buffer += PcktLength_SF[node.parameters.sf-7]
                print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
                node.acklost = node.acklost + 1
                node.lstretans += 1
                global nrACKLost
                nrACKLost += 1
          if node.packet[bs].collided == 0 and not node.packet[bs].lost:
	        packetsRecBS[bs].append(node.packet[bs].seqNr)
                node.recv = node.recv + 1
                node.lstretans = 0
                global nrReceived
                nrReceived = nrReceived + 1
       
          # complete packet has been received by base station
          # can remove it
	  for bs in range(0, nrBS):
            if (node in packetsAtBS[bs]):
                packetsAtBS[bs].remove(node)
                # reset the packet
                node.packet[bs].collided = 0
                node.packet[bs].processed = 0
                node.packet[bs].lost = False
                node.packet[bs].acked = 0
                node.packet[bs].acklost = 0



if len(sys.argv) >= 1:
       full_collision = bool(int(sys.argv[1]))
       experiment = 0"
else:
        print "usage: ./OneBS.py [collision]"
        print "experiment 0 and 1 use 1 frequency only"
        exit(-1)

	

# list of base stations

   


# maximum number of packets the BS can receive at the same time
maxBSReceives = 8





# maximum number of packets the BS can receive at the same time
maxBSReceives = 8

# max distance: 300m in city, 3000 m outside (5 km Utz experiment)
# also more unit-disc like according to Utz
bsId = 1
nrCollisions = 0
nrReceived = 0
nrProcessed = 0
nrLost = 0
nrLostError = 0
nrNoACK = 0
nrACKLost = 0

# global value of packet sequence numbers
packetSeq = 0

# list of received packets
recPackets=[]
collidedPackets=[]
lostPackets = []

Ptx = 9.75
gamma = 2.08
d0 = 40.0
var = 2.0           # variance ignored for now
Lpld0 = 127.41
GL = 0

sensi = np.array([sf7,sf8,sf9,sf10,sf11,sf12])
## figure out the minimal sensitivity for the given experiment
minsensi = -200.0


Lpl = Ptx - minsensi
print "amin", minsensi, "Lpl", Lpl
maxDist = d0*(math.e**((Lpl-Lpld0)/(10.0*gamma)))
print "maxDist:", maxDist

maxX = 2 * maxDist * math.sin(60*(math.pi/180)) # == sqrt(3) * maxDist
print "maxX ", maxX
maxY = 2 * maxDist * math.sin(30*(math.pi/180)) # == maxdist
print "maxY", maxY



if experiment in [0,1,4,6]:
    minsensi = sensi[5,2]  # 5th row is SF12, 2nd column is BW125
elif experiment == 2:
    minsensi = -112.0   # no experiments, so value from datasheet
elif experiment == [3,5]:
    minsensi = np.amin(sensi) ## Experiment 3 can use any setting, so take minimum
# base station placement
bsx = maxDist+10
bsy = maxDist+10
xmax = bsx + maxDist + 20
ymax = bsy + maxDist + 20

                                            #ici

bs = []
nodes = []
# list of packets at each base station, init with 0 packets
packetsAtBS = []
packetsRecBS = []
env = simpy.Environment()


# prepare graphics and add sink
if (graphics == 1):
    plt.ion()
    plt.figure()
    ax = plt.gcf().gca()
    ax.add_patch(Rectangle((0, 0), maxX, maxY, fill=None, alpha=1))
# Ouverture d'un fichier d'informations en *lecture*:  
fichier = open("MulNoeuds.txt", "r")

j = 0
i = 0

for ligne in fichier:
   if j == 0:
      y = ligne.split()
      nrNodes = int(y[0])
      nrBS = int(y[1])
      SF = int(y[2])
      BW = int(y[3])
      avgSendTime = int(y[4])
      simtime = int(y[5])
      
   else:
     if j <= nrBS:
        z = ligne.split()
        b = myBS(j, int(z[0]),int(z[1]))
        bs.append(b)
        packetsAtBS.append([])
        packetsRecBS.append([])     
     else:
      if i < nrNodes:
        x = ligne.split()
        node = myNode(i, avgSendTime,avgSendTime,int(x[2]),float(x[0]),float(x[1]))
        nodes.append(node)
        env.process(transmit(env,node))
        i = i + 1          
   j = j + 1

    
# Fermeture du fichier
fichier.close()


print "Nodes:", nrNodes
print "AvgSendTime (exp. distributed):",avgSendTime
print "Experiment: ", experiment
print "Simtime: ", simtime
print "Full Collision: ", full_collision

# global stuff

nodeder1 = [0 for i in range(0,nrNodes)]
nodeder2 = [0 for i in range(0,nrNodes)]
tempdists = [0 for i in range(0,nrNodes)]
SFdistribution = [0 for x in range(0,6)]
BWdistribution = [0 for x in range(0,3)]
CRdistribution = [0 for x in range(0,4)]
TXdistribution = [0 for x in range(0,13)]





#prepare show
if (graphics == 1):
    plt.xlim([0, xmax])
    plt.ylim([0, ymax])
    plt.draw()
    plt.show()

# store nodes and basestation locations
with open('nodes.txt', 'w') as nfile:
    for node in nodes:
        nfile.write('{x} {y} {id}\n'.format(**vars(node)))

with open('basestation.txt', 'w') as bfile:
    for basestation in bs:
        bfile.write('{x} {y} {id}\n'.format(**vars(basestation)))

# start simulation
env.run(until=simtime)

# compute energy
energy = 0.0
mA = 90    # current draw for TX = 17 dBm
V = 3     # voltage XXX
sent = 0
#for i in range(0,nrNodes):   Statistique pour chaque noeud 
#    print "sent ", nodes[i].sent
#    sent = sent + nodes[i].sent
#    energy = (energy + nodes[i].packet.rectime * mA * V * nodes[i].sent)/1000.0

for i in range(0,nrNodes):
#    print "sent ", nodes[i].sent
 sent = sent + nodes[i].sent


def mynRecTime(node):
    moyenne = 0
    for i in range(0,len(node.packet)):
        moyenne = moyenne + node.packet[i].rectime
    return moyenne


#energy = (energy + ((nodes[i].packet.rectime * nodes[i].sent * mA) + V * (nodes[i].rxtime * RX)))/1e3

# compute energy
# Transmit consumption in mA from -2 to +17 dBm
TX = [22, 22, 22, 23,                                      # RFO/PA0: -2..1
      24, 24, 24, 25, 25, 25, 25, 26, 31, 32, 34, 35, 44,  # PA_BOOST/PA1: 2..14
      82, 85, 90,                                          # PA_BOOST/PA1: 15..17
      105, 115, 125]                                       # PA_BOOST/PA1+PA2: 18..20
RX = 16
V = 3.0     # voltage XXX
txpow = 14
sent = sum(n.sent for n in nodes)

energy = sum((( mynRecTime(node) * node.sent * TX[int(txpow)+2])+(node.rxtime * RX)) * V  for node in nodes)  / 1e3

# print stats and save into file
# print "nrCollisions ", nrCollisions
# print list of received packets
#print recPackets
print "energy (in mJ): ", energy
print "sent packets: ", sent
print "collisions: ", len(collidedPackets)
print "received packets: ", len(recPackets)
print "processed packets: ", nrProcessed
print "lost packets: ", len(lostPackets)
print "Bad CRC: ", nrLostError
print "NoACK packets: ", nrNoACK
# data extraction rate
der1 = (sent-nrCollisions)/float(sent) if sent!=0 else 0
print "DER:", der1
der2 = (nrReceived)/float(sent) if sent!=0 else 0
print "DER method 2:", der2

#print "sent packets: ", sent
#print "sent packets-collisions: ", sent-nrCollisions
#print "received packets: ", len(recPackets)
for i in range(0,nrBS):
    print "packets at BS ",i, ":", len(packetsRecBS[i])
print "sent packets: ", packetSeq

# data extraction rate per node
for i in range(0,nrNodes):
    tempdists[i] = nodes[i].distances
    nodeder1[i] = ((nodes[i].sent-nodes[i].coll)/(float(nodes[i].sent)) if float(nodes[i].sent)!=0 else 0)
    nodeder2[i] = (nodes[i].recv/(float(nodes[i].sent)) if float(nodes[i].sent)!=0 else 0)
# calculate the fairness indexes per node
nodefair1 = (sum(nodeder1)**2/(nrNodes*sum([i*float(j) for i,j in zip(nodeder1,nodeder1)])) if (sum([i*float(j) for i,j in zip(nodeder1,nodeder1)]))!=0 else 0)
nodefair2 = (sum(nodeder2)**2/(nrNodes*sum([i*float(j) for i,j in zip(nodeder2,nodeder2)])) if (sum([i*float(j) for i,j in zip(nodeder2,nodeder2)]))!=0 else 0)



# this can be done to keep graphics visible
if (graphics == 1):
    raw_input('Press Enter to continue ...')

# save experiment data into a dat file that can be read by e.g. gnuplot
# name of file would be:  exp0.dat for experiment 0
print "============================"
print "SFdistribution: ", SFdistribution
print "BWdistribution: ", BWdistribution
print "CRdistribution: ", CRdistribution
print "TXdistribution: ", TXdistribution
print "CollectionTime: ", env.now

# save experiment data into a dat file that can be read by e.g. gnuplot
# name of file would be:  exp0.dat for experiment 0
fname = str("confirmablelorawan") + ".dat"
print fname
if os.path.isfile(fname):
     res= "\n" + str(sys.argv[5]) + ", " + str(full_collision) + ", " + str(nrNodes) + ", " + str(avgSendTime) + ", " + str(datasize) + ", " + str(sent) + ", "  + str(nrCollisions) + ", "  + str(nrLost) + ", "  + str(nrLostError) + ", " +str(nrNoACK) + ", " +str(nrACKLost) + ", " + str(env.now)+ ", " + str(der1) + ", " + str(der2)  + ", " + str(energy) + ", "  + str(nodefair1) + ", "  + str(nodefair2) + ", "  + str(SFdistribution)
else:
     res = "#randomseed, collType, nrNodes, TransRate, DataSize, nrTransmissions, nrCollisions, nrlost, nrlosterror, nrnoack, nracklost, CollectionTime, DER1, DER2, OverallEnergy, nodefair1, nodefair2, sfdistribution\n" + str(sys.argv[5]) + ", " + str(full_collision) + ", " + str(nrNodes) + ", " + str(avgSendTime) + ", " + str(datasize) + ", " + str(sent) + ", "  + str(nrCollisions) + ", "  + str(nrLost) + ", "  + str(nrLostError) + ", " +str(nrNoACK) + ", " +str(nrACKLost) + ", " + str(env.now)+ ", " + str(der1) + ", " + str(der2)  + ", " + str(energy) + ", "  + str(nodefair1) + ", "  + str(nodefair2) + ", "  + str(SFdistribution)
newres=re.sub('[^#a-zA-Z0-9 \n\.]','',res)
print newres
with open(fname, "a") as myfile:
    myfile.write(newres)
myfile.close()


