#!/usr/bin/env python

import csv

def run():

    usernames = {}
    with open('ngo-usernames.csv', 'rb') as h:
        names = csv.reader(h, delimiter=',', quotechar="\"")
        for (name,) in names: 
            usernames[name] = True

    def userType(name):
        if name in usernames: 
            return "Organisation"
        else:
            return "Volunteer"

    with open('Test.csv', 'wb') as g: 
        with open('2015 Reviews.xlsx - 160325 Reviews.csv', 'rb') as f:        
            r = csv.reader(f, delimiter=',', quotechar="\"")
            w = csv.writer(g, delimiter=',', quotechar="\"")

            # Read / write headers
            row = r.next()
            w.writerow(row + ["User Type"])
            
            lastrow = False
            for row in r:
                (projectid,taskid,corrections,grammar,spelling,consistency,comment,user) = row
                if (projectid in ['','null'] and comment in ['','null']): 
                    pass
                elif (projectid in ['','null'] and lastrow):
                    lastrow = [lastrow[0],lastrow[1],lastrow[2],lastrow[3],lastrow[4],lastrow[5],lastrow[6]+' '+comment,lastrow[7]]
                elif lastrow:
                    w.writerow(lastrow + [userType(lastrow[7])])
                    lastrow = row
                else:
                    lastrow = row

if __name__ == "__main__":
    run()
    
