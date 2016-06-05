#!/usr/bin/env python

bands = [(.15,34000),(.25,45000),(.3,71000)]

test =((0.15 * min($deciles.$C2,37000) +
        0.25 * max(0,min( $deciles.$C2 - 37000, 45000-37000)) +
        1/3 * max(0,min( $deciles.$C2 - 45000))) / 12)


def monthly(income):
    band1 = 0.15 * min(income,37000) / 12 
    band2 = 0.25 * max(0,min(income - 37000, 45000 - 37000)) / 12 
    band3 = 0.33 * max(0,income - 45000.0) / 12
    print "Contribution from band1: %s\nContribution from band2: %s\nContribution from band3: %s\n" % (band1, band2, band3)
