#!/usr/bin/env python

import csv

def run(filename):
    with open('Test.csv', 'wb') as g: 
        with open(filename, 'rb') as f:        
            r = csv.reader(f, delimiter=',', quotechar="\"")
            w = csv.writer(g, delimiter=',', quotechar="\"")

            # Write field names
            # w.writerow(r.fieldnames)
            
            lastrow = False
            for row in r:
                (projectid,taskid,corrections,grammar,spelling,consistency,comment,user) = row
                if (projectid in ['','null'] and comment in ['','null']): 
                    pass
                elif (projectid in ['','null'] and lastrow):
                    lastrow = (lastrow[0],lastrow[1],lastrow[2],lastrow[3],lastrow[4],lastrow[5],lastrow[6]+' '+comment,lastrow[7])
                elif lastrow:
                    w.writerow(lastrow)
                    lastrow = row
                else:
                    lastrow = row

                    
