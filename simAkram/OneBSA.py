#!/usr/bin/env python2
# -*- coding: utf-8 -*-
"""
 LoRaSim 0.2.1: simulate collisions in LoRa
 Copyright © 2016 Thiemo Voigt <thiemo@sics.se> and Martin Bor <m.bor@lancaster.ac.uk>

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
   ./loraDir.py <nodes> <avgsend> <experiment> <simtime> [collision]
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
from datetime import datetime
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
import sqlite3

int collisionConse = 0;

try:
    sqliteConnection = sqlite3.connect('testdatabase.db')

    cursor = sqliteConnection.cursor()
    print("Database created and Successfully Connected to SQLite")

except sqlite3.Error as error:
    print("Error while connecting to sqlite", error)
    """
finally:
    if (sqliteConnection):
        sqliteConnection.close()
        print("The SQLite connection is closed")
        """
# turn on/off graphics

#test sqlite 
sqlite_insert_query = """INSERT INTO myTable
                          (id, name) 
                           VALUES 
                          (5,"mohamed")"""

count = cursor.execute(sqlite_insert_query)
sqliteConnection.commit()
print("Record inserted successfully into myTable table ", cursor.rowcount)

sqlite_select_query = """SELECT * from myTable"""
cursor.execute(sqlite_select_query)
records = cursor.fetchall()


print("Total rows are:  ", len(records))
print("Printing each row")
for row in records:
    print("Id: ", row[0])
    print("Name: ", row[1]) 



cursor.close()


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
    chanlindex=[872000000, 864000000, 860000000,868000000].index(packet.freq)
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
    sfCollisions = open("CollisionsOneBS.txt", "w")
    now = datetime.now()
    date_time = now.strftime("%m/%d/%Y, %H:%M:%S")
    sfCollisions.write("Date de la simulation : {} \n".format(date_time))
    col = 0 # flag needed since there might be several collisions for packet
    processing = 0
    for i in range(0,len(packetsAtBS)):
        if packetsAtBS[i].packet.processed == 1:
            processing = processing + 1
    if (processing > maxBSReceives):
        print "too long:", len(packetsAtBS)
        packet.processed = 0
    else:
        packet.processed = 1

    if packetsAtBS:
        print "CHECK node {} (sf:{} bw:{} freq:{:.6e}) others: {}".format(
             packet.nodeid, packet.sf, packet.bw, packet.freq,
             len(packetsAtBS))
        sfCollisions.write("CHECK node {} (sf:{} bw:{} freq:{:.6e}) others: {}".format(
             packet.nodeid, packet.sf, packet.bw, packet.freq,
             len(packetsAtBS)))
        
        for other in packetsAtBS:
            if other.nodeid != packet.nodeid:
               print "\n    >> node {} (sf:{} bw:{} freq:{:.6e})".format(
                   other.nodeid, other.packet.sf, other.packet.bw, other.packet.freq)
               sfCollisions.write(">> node {} (sf:{} bw:{} freq:{:.6e})".format(
                   other.nodeid, other.packet.sf, other.packet.bw, other.packet.freq))
               # simple collision
               if frequencyCollision(packet, other.packet,sfCollisions) \
                   and sfCollision(packet, other.packet, sfCollisions):
                   if full_collision:
                       if timingCollision(packet, other.packet, sfCollisions):
                           # check who collides in the power domain
                           c = powerCollision(packet, other.packet, sfCollisions)
                           # mark all the collided packets
                           # either this one, the other one, or both
                           for p in c:
                               p.collided = 1
                               if p == packet:
                                   col = 1
                       else:
                           # no timing collision, all fine
                           pass
                   else:
                       packet.collided = 1
                       other.packet.collided = 1  # other also got lost, if it wasn't lost already
                       col = 1
        return col
    sfCollisions.close()
    return 0

#
# frequencyCollision, conditions
#
#        |f1-f2| <= 120 kHz if f1 or f2 has bw 500
#        |f1-f2| <= 60 kHz if f1 or f2 has bw 250
#        |f1-f2| <= 30 kHz if f1 or f2 has bw 125
def frequencyCollision(p1,p2,sfCollisions):
    if (abs(p1.freq-p2.freq)<=120 and (p1.bw==500 or p2.bw==500)):
        print "frequency coll 500"
        sfCollisions.write("\n frequency coll 500")
        return True
    elif (abs(p1.freq-p2.freq)<=60 and (p1.bw==250 or p2.bw==250)):
        print "frequency coll 250"
        sfCollisions.write("\n frequency coll 250\n")
        return True
    else:
        if (abs(p1.freq-p2.freq)<=30):
            print "frequency coll 125"
            sfCollisions.write("\n frequency coll 125\n")
            return True
        #else:
    print "no frequency coll"
    sfCollisions.write("\n No frequency coll\n")
    return False

def sfCollision(p1, p2, sfCollisions):

    if p1.sf == p2.sf:
        print "collision sf node {} and node {}".format(p1.nodeid, p2.nodeid)
        sfCollisions.write("collision sf node {} and node {}".format(p1.nodeid, p2.nodeid))
        # p2 may have been lost too, will be marked by other checks
        return True
    print "no sf collision"
    sfCollisions.write("\n no sf collision\n")
    return False


def powerCollision(p1, p2, sfCollisions):
    powerThreshold = 6 # dB
    print "pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2))
    sfCollisions.write("pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2)))
    if abs(p1.rssi - p2.rssi) < powerThreshold:
        print "collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid)
        sfCollisions.write("\n collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid))
        # packets are too close to each other, both collide
        # return both packets as casualties
        return (p1, p2)
    elif p1.rssi - p2.rssi < powerThreshold:
        # p2 overpowered p1, return p1 as casualty
        print "collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid)
        sfCollisions.write("\n collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid))
        return (p1,)
    print "p1 wins, p2 lost"
    sfCollisions.write("\n p1 wins, p2 lost\n")
    # p2 was the weaker packet, return it as a casualty
    return (p2,)


def timingCollision(p1, p2, sfCollisions):
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
    print "collision timing node {} ({},{},{}) node {} ({},{})".format(
        p1.nodeid, env.now - env.now, p1_cs - env.now, p1.rectime,
        p2.nodeid, p2.addTime - env.now, p2_end - env.now
    )
    sfCollisions.write("\n collision timing node {} ({},{},{}) node {} ({},{})".format(
        p1.nodeid, env.now - env.now, p1_cs - env.now, p1.rectime,
        p2.nodeid, p2.addTime - env.now, p2_end - env.now
    ))
    if p1_cs < p2_end:
        # p1 collided with p2 and lost
        print "not late enough"
        sfCollisions.write("\n not late enough\n")
        return True
    print "saved by the preamble"
    sfCollisions.write("\n saved by the preamble\n")
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
    print "sf", sf, " cr", cr, "pl", pl, "bw", bw
    payloadSymbNB = 8 + max(math.ceil((8.0*pl-4.0*sf+28+16-20*H)/(4.0*(sf-2*DE)))*(cr+4),0)
    Tpayload = payloadSymbNB * Tsym
    return Tpream + Tpayload

#
# this function creates a node
#
class myNode():
    def __init__(self, nodeid, bs, period, packetlen):
        self.nodeid = nodeid
        self.period = period
        self.bs = bs
	self.buffer = packetlen
        self.first = 1
        self.period = period
        self.lstretans = 0
        self.sent = 0
        self.coll = 0
        self.lost = 0
        self.noack = 0
        self.acklost = 0
        self.recv = 0
        self.losterror = 0
        self.rxtime = 0
        self.x = 0
        self.y = 0
        self.SFs = [0,0,0,0,0,0]
        # this is very complex prodecure for placing nodes
        # and ensure minimum distance between each pair of nodes
        found = 0
        rounds = 0
        global nodes
        while (found == 0 and rounds < 100):
            a = random.random()
            b = random.random()
            if b<a:
                a,b = b,a
            posx = b*maxDist*math.cos(2*math.pi*a/b)+bsx
            posy = b*maxDist*math.sin(2*math.pi*a/b)+bsy
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
                            exit(-1)
            else:
                print "first node"
                self.x = posx
                self.y = posy
                found = 1
        self.dist = np.sqrt((self.x-bsx)*(self.x-bsx)+(self.y-bsy)*(self.y-bsy))
        print('node %d' %nodeid, "x", self.x, "y", self.y, "dist: ", self.dist)

        self.packet = myPacket(self.nodeid, packetlen, self.dist)
        self.sent = 0

        # graphics for node
        global graphics
        if (graphics == 1):
            global ax
            ax.add_artist(plt.Circle((self.x, self.y), 2, fill=True, color='blue'))

#
# this function creates a packet (associated with a node)
# it also sets all parameters, currently random
#
class myPacket():
    def __init__(self, nodeid, plen, distance):
        global experiment
        global Ptx
        global gamma
        global d0
        global var
        global Lpld0
        global GL
        global SFs
        
        
        self.nodeid = nodeid
        self.txpow = Ptx

        # randomize configuration values
        self.sf = random.randint(6,12)
        self.cr = random.randint(1,4)
        self.bw = random.choice([125, 250, 500])

        """ if experiment == 6: 
           self.sf =SF
           self.cr = 1
           self.bw = BW """
 
           
        
        # for experiment 3 find the best setting
        # OBS, some hardcoded values
        Prx = self.txpow  ## zero path loss by default

        # log-shadow
        Lpl = Lpld0 + 10*gamma*math.log10(distance/d0)
        print "Lpl:", Lpl
        Prx = self.txpow - GL - Lpl


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

        print "frequency" ,self.freq, "symTime ", self.symTime
        print "bw", self.bw, "sf", self.sf, "cr", self.cr, "rssi", self.rssi
        self.rectime = airtime(self.sf,self.cr,self.pl,self.bw)
        print "rectime node ", self.nodeid, "  ", self.rectime
        # denote if packet is collided
        self.collided = 0
        self.processed = 0
	self.lost = False
        self.perror = False
        self.acked = 0
        self.acklost = 0

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
        if (node in packetsAtBS):
            print "ERROR: packet already in"
        else:
            sensitivity = sensi[node.packet.sf - 7, [125,250,500].index(node.packet.bw) + 1]
            if node.packet.rssi < sensitivity:
                print "node {}: packet will be lost".format(node.nodeid)
                node.packet.lost = True
            else:
                node.packet.lost = False
		if (per(node.packet.sf,node.packet.bw,node.packet.cr,node.packet.rssi,node.packet.pl) < random.uniform(0,1)):
                    # OK CRC
                    node.packet.perror = False
                else:
                    # Bad CRC
                    node.packet.perror = True
            # adding packet if no collision
            if (checkcollision(node.packet)==1):
                    node.packet.collided = 1
            else:
                    node.packet.collided = 0
        packetsAtBS.append(node)
        node.packet.addTime = env.now

        yield env.timeout(node.packet.rectime)
	if (node.packet.lost == 0\
                and node.packet.perror == False\
                and node.packet.collided == False\
                and checkACK(node.packet)):
                 node.packet.acked = 1
                 # the packet can be acked
                 # check if the ack is lost or not
                 if((14 - Lpld0 - 10*gamma*math.log10(node.dist/d0) - np.random.normal(-var, var)) > sensi[node.packet.sf-7, [125,250,500].index(node.packet.bw) + 1]):
                    #the ack is not lost
                    node.packet.acklost = 0
                 else:
                    #ack is lost
                    node.packet.acklost = 1
        else:
             node.packet.acked = 0

        if node.packet.processed == 1:
            global nrProcessed
            nrProcessed = nrProcessed + 1
        if node.packet.lost:
            global nrLost
            nrLost += 1
            node.SFs[node.packet.sf-7] = node.SFs[node.packet.sf-7] - 1
        if node.packet.collided == 1:
	    node.coll = node.coll + 1
            node.lstretans += 1
            global nrCollisions
            nrCollisions = nrCollisions +1
            node.SFs[node.packet.sf-7] = node.SFs[node.packet.sf-7] - 1
        if node.packet.acked == 0:
            #node.buffer += PcktLength_SF[node.parameters.sf-7]
            #print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
            node.noack = node.noack + 1
            node.lstretans += 1
            global nrNoACK
            nrNoACK += 1
        if node.packet.acklost == 1:
            #node.buffer += PcktLength_SF[node.parameters.sf-7]
            #print "node {0.nodeid} buffer {0.buffer} bytes".format(node)
            node.acklost = node.acklost + 1
            node.lstretans += 1
            global nrACKLost
            nrACKLost += 1
        if node.packet.collided == 0 and not node.packet.lost:
            node.lstretans = 0
            global nrReceived
            nrReceived = nrReceived + 1
            node.SFs[node.packet.sf-7] = node.SFs[node.packet.sf-7] + 1
            
        
        if node.coll >= 1:
            # 1ère version ok
            """
            print "J'ai changé de SF : node", node.nodeid
            node.packet.sf = random.randint(6,12)
            node.packet.cr = random.randint(1,4)
            node.packet.bw = random.choice([125, 250, 500])
            """

            # 2ème version ok
            """
            p = random.randint(0,1)
            if p >= 0.40:
                 print "J'ai changé de SF : node", node.nodeid
                 node.packet.sf = random.randint(6,12)
                 node.packet.cr = random.randint(1,4)
                 node.packet.bw = random.choice([125, 250, 500])
            else:
                 print "J'ai pas changé de SF je retante avec le meme SF : node", node.nodeid
            """

            
            
            # 3ème version 
            taille = len(node.SFs)
            max = 0
            for i in range(1,taille):
                if node.SFs[max] <= node.SFs[i]: 
                   max = i 
            node.packet.sf = node.SFs[max] + 7
            print "J'ai changé le SF du noeud n° ",node.nodeid
            print "Nouvelle SF ", node.packet.sf 
            
                 
               


        # complete packet has been received by base station
        # can remove it
        if (node in packetsAtBS):
            packetsAtBS.remove(node)
            # reset the packet
        node.packet.collided = 0
        node.packet.processed = 0
        node.packet.lost = False
	node.packet.acked = 0
        node.packet.acklost = 0

#
# "main" program
#
# Nouveaux tableaux 
SFs = [0,0,0,0,0,0]


print "Donner Votre choix"
print "Taper 0 pour le mode compatible LoRaSim"
print "Taper 1 pour le mode AkramSim"
i = input("Donner votre choix :   ")
if i == 0:
    print "************* LoRaSim **************"
    nrNodes = input("Saisissez le nombre de neouds :   ")
    avgSendTime = input("Average send time :   ")
    experiment = input("Experiment :   ")
    simtime = input("Simulation time :   ")
    dataSize = input("Datasize :   ")
    full_collision = input("full collision :   ")
     # if len(sys.argv) >= 7:
     #     nrNodes = int(sys.argv[1])
     #     avgSendTime = int(sys.argv[2])
     #     experiment = int(sys.argv[3])
     #     simtime = int(sys.argv[4])
     #     dataSize = int(sys.argv[5])
     #     if len(sys.argv) > 5:
     #         full_collision = bool(int(sys.argv[6]))
     # else:
     #   print "usage: ./OneBS.py <nodes> <avgsend> <experiment> <simtime> <Datasize Max> [collision]"
     #   print "experiment 0 and 1 use 1 frequency only"
     #   exit(-1)

	
    print "Nodes:", nrNodes
    print "AvgSendTime (exp. distributed):",avgSendTime
    print "Experiment: ", experiment
    print "Simtime: ", simtime
    print "Full Collision: ", full_collision

else:

    #if len(sys.argv) >= 8:
    #    nrNodes = int(sys.argv[1])
    #    avgSendTime = int(sys.argv[2])
    #    simtime = int(sys.argv[3])
    #    dataSize = int(sys.argv[4]) 
    #    SF = int(sys.argv[5])
    #    BW = int(sys.argv[6]) 
    #    if len(sys.argv) > 6:
    #        full_collision = bool(int(sys.argv[7]))
    print "************* AkramSim **************"
    nrNodes = input("Saisissez le nombre de neouds :   ")
    avgSendTime = input("Average send time :   ")
    simtime = input("Simulation time :   ")
    dataSize = input("Datasize Max:   ")
    SF = input("Facteur d'étalement :   ")
    BW = input("Bande passante  :   ")
    full_collision = input("full collision :   ")
    print "Nodes:", nrNodes
    print "AvgSendTime (exp. distributed):",avgSendTime
    print "Simtime: ", simtime
    print "Full Collision: ", full_collision
    print "SF", SF
    print "BW", BW
    print "datasize Max", dataSize
    experiment = 6
    #else:
    #    print "usage: ./OneBS.py <nodes> <avgsend>  <simtime> <datasize Max> <SF> <BW> [collision]"
    #    print "experiment 0 and 1 use 1 frequency only"
    #    exit(-1)


# global stuff
#Rnd = random.seed(12345)
nodes = []
packetsAtBS = []
env = simpy.Environment()

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

Ptx = 9.75
gamma = 2.08
d0 = 40.0
var = 2.0           # variance ignored for now
Lpld0 = 127.41
GL = 0

sensi = np.array([sf7,sf8,sf9,sf10,sf11,sf12])
if experiment in [0,1,4,6]:
    minsensi = sensi[5,2]  # 5th row is SF12, 2nd column is BW125
elif experiment == 2:
    minsensi = -112.0   # no experiments, so value from datasheet
elif experiment in [3,5]:
    minsensi = np.amin(sensi) ## Experiment 3 can use any setting, so take minimum
Lpl = Ptx - minsensi
print "amin", minsensi, "Lpl", Lpl
maxDist = d0*(math.e**((Lpl-Lpld0)/(10.0*gamma)))
print "maxDist:", maxDist

# base station placement
bsx = maxDist+10
bsy = maxDist+10
xmax = bsx + maxDist + 20
ymax = bsy + maxDist + 20

# prepare graphics and add sink
if (graphics == 1):
    plt.ion()
    plt.figure()
    ax = plt.gcf().gca()
    # XXX should be base station position
    ax.add_artist(plt.Circle((bsx, bsy), 3, fill=True, color='green'))
    ax.add_artist(plt.Circle((bsx, bsy), maxDist, fill=False, color='green'))


for i in range(0,nrNodes):
    # myNode takes period (in ms), base station id packetlen (in Bytes)
    # 1000000 = 16 min
    size = random.randint(1000,dataSize)
    node = myNode(i,bsId, avgSendTime,size)
    nodes.append(node)
    env.process(transmit(env,node))

#prepare show
if (graphics == 1):
    plt.xlim([0, xmax])
    plt.ylim([0, ymax])
    plt.draw()
    plt.show()

# start simulation
env.run(until=simtime)

# print stats and save into file
print "nrCollisions ", nrCollisions

# compute energy
# Transmit consumption in mA from -2 to +17 dBm
TX = [22, 22, 22, 23,                                      # RFO/PA0: -2..1
      24, 24, 24, 25, 25, 25, 25, 26, 31, 32, 34, 35, 44,  # PA_BOOST/PA1: 2..14
      82, 85, 90,                                          # PA_BOOST/PA1: 15..17
      105, 115, 125]                                       # PA_BOOST/PA1+PA2: 18..20
RX = 16
V = 3.0     # voltage XXX
sent = sum(n.sent for n in nodes)
energy = sum(((node.packet.rectime * node.sent * TX[int(node.packet.txpow)+2])+(node.rxtime * RX)) * V  for node in nodes)  / 1e3

statistiques = open("statistiquesOneBS.txt", "w")
now = datetime.now()
date_time = now.strftime("%m/%d/%Y, %H:%M:%S")
statistiques.write("Date de la simulation : {} \n".format(date_time))
print "energy (in mJ): ", energy
statistiques.write("energy (in mJ): {} \n".format(energy))
print "sent packets: ", sent
statistiques.write("sent packets: {} \n".format(sent))
print "collisions: ", nrCollisions
statistiques.write("collisions: {} \n".format(nrCollisions))
print "received packets: ", nrReceived
statistiques.write("received packets: {} \n".format(nrReceived))
print "processed packets: ", nrProcessed
statistiques.write("processed packets: {} \n".format(nrProcessed))
print "lost packets: ", nrLost
statistiques.write("lost packets: {} \n".format(nrLost))
print "NoACK packets: ", nrNoACK
statistiques.write("NoACK packets: {} \n".format(nrNoACK))

# data extraction rate
der = (sent-nrCollisions)/float(sent)
print "DER:", der
statistiques.write("DER : {} \n".format(der))
der = (nrReceived)/float(sent)
print "DER method 2:", der
statistiques.write("DER method 2 : {} \n".format(der))

statistiques.close()
# this can be done to keep graphics visible
if (graphics == 1):
    raw_input('Press Enter to continue ...')

# save experiment data into a dat file that can be read by e.g. gnuplot
# name of file would be:  exp0.dat for experiment 0
fname = "exp" + str(experiment) + ".dat"
print fname
if os.path.isfile(fname):
    res = "\n" + str(nrNodes) + " " + str(nrCollisions) + " "  + str(sent) + " " + str(energy)
else:
    res = "#nrNodes nrCollisions nrTransmissions OverallEnergy\n" + str(nrNodes) + " " + str(nrCollisions) + " "  + str(sent) + " " + str(energy)
with open(fname, "a") as myfile:
    myfile.write(res)
myfile.close()

# with open('nodes.txt','w') as nfile:
#     for n in nodes:
#         nfile.write("{} {} {}\n".format(n.x, n.y, n.nodeid))
# with open('basestation.txt', 'w') as bfile:
#     bfile.write("{} {} {}\n".format(bsx, bsy, 0))
