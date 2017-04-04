#!/usr/bin/env python

import hashlib

# g = grass
# w = water

# Map:
#
# ggg
# gww
# ggw

world = [[{'terrain' : 'grass',
           'coordinate' : (0,0),
           'items' : []},
          {'terrain' : 'grass',
           'coordinate' : (0,1),
           'items' : []},
          {'terrain' : 'grass',
           'coordinate' : (0,2),
           'items' : []}],
         [{'terrain' : 'grass',
           'coordinate' : (1,0),
           'items' : ['sword of damacles']},
          {'terrain' : 'water',
           'coordinate' : (1,1),
           'items' : []},
          {'terrain' : 'grass',
           'coordinate' : (1,2),
           'items' : []}],
         [{'terrain' : 'water',
           'coordinate' : (2,0),
           'items' : []},
          {'terrain' : 'water',
           'coordinate' : (2,1),
           'items' : []},
          {'terrain' : 'grass',
           'coordinate' : (2,2),
           'items' : ['gordian knot']}]]

def find_location(location):
    for row in world:
        for elt in row:
            hsh = hashlib.md5()
            hsh.update(str(elt))
            digest = hsh.hexdigest()
            if location['location'] == digest:
                return elt
    return {'error' : "Invalid location",
            'msg' : "There is no location with that key"}

def get_location(location):
    if location:
        record = find_location(location)
    else:
        record = world[0][0]
    return dict(record)

def server(request,location=None,items=[]):
    if request == 'get_coordinates':
        record = get_location(location)
        hsh = hashlib.md5()
        hsh.update(str(record))            
        record['location'] = hsh.hexdigest()
        return record
    elif request == 'go_west':
        record = get_location(location)
        if 'error' in record:
            return record
        (x,y) = record['coordinate']
        if x > 0:
            hsh = hashlib.md5()
            new_record = dict(world[x-1][y])
            if new_record['terrain'] == 'water':
                return {'error' : "drowning",
                        'msg' : "You will drown now that you walked into terribly deep water"}
            hsh.update(str(new_record))
            new_record['location'] = hsh.hexdigest()
            return new_record
        else:
            return {'error' : "Out of bounds",
                    'msg' : "You have fallen off the edge of the world and have died."}
    elif request == 'go_north':
        record = get_location(location)
        if 'error' in record:
            return record
        (x,y) = record['coordinate']
        if y < 2:
            hsh = hashlib.md5()
            new_record = dict(world[x][y+1])
            if new_record['terrain'] == 'water':
                return {'error' : "drowning",
                        'msg' : "You will drown now that you walked into terribly deep water"}
            hsh.update(str(new_record))
            new_record['location'] = hsh.hexdigest()
            return new_record
        else:
            return {'error' : "Out of bounds",
                    'msg' : "You have fallen off the edge of the world and have died."}
    elif request == 'go_east':
        record = get_location(location)
        if 'error' in record:
            return record
        (x,y) = record['coordinate']
        if x < 2:
            hsh = hashlib.md5()
            new_record = dict(world[x+1][y])
            if new_record['terrain'] == 'water':
                return {'error' : "drowning",
                        'msg' : "You will drown now that you walked into terribly deep water"}
            hsh.update(str(new_record))
            new_record['location'] = hsh.hexdigest()
            return new_record
        else:
            return {'error' : "Out of bounds",
                    'msg' : "You have fallen off the edge of the world and have died."}
    elif request == 'go_south':
        record = get_location(location)
        if 'error' in record:
            return record
        (x,y) = record['coordinate']
        if y > 0:
            hsh = hashlib.md5()
            new_record = dict(world[x][y-1])
            if new_record['terrain'] == 'water':
                return {'error' : "drowning",
                        'msg' : "You will drown now that you walked into terribly deep water"}
            hsh.update(str(new_record))
            new_record['location'] = hsh.hexdigest()
            return new_record
        else:
            return {'error' : "Out of bounds",
                    'msg' : "You have fallen off the edge of the world and have died."}
    elif request == 'pick_up':
        record = get_location(location)
        items = record['items']
        if items > 0:
            item = items[0]
            hsh = hashlib.md5()
            hsh.update(item)
            return hsh.hexdigest()
        else:
            return {'error' : "Nothing here",
                    'msg' : "There is nothing here to pick up"}
    elif request == 'slice' :
        hsh = hashlib.md5()
        hsh.update('gordian knot')
        a = hsh.hexdigest()
        hsh = hashlib.md5()
        hsh.update('sword of damacles')
        b = hsh.hexdigest()
        if (a in items and b in items):
            return {'success' : "Congragulations",
                    'msg' : "One way or another, you have successfully slides the Gordian knot"}
        else:
            return {'error' : "incomplete",
                    'msg' : "You don't have all the necessary items"}
    else:
        return {'error' : "unrecognised request",
                'msg' : "The request: " + str(request) + " is not recognised."}


if __name__ == "__main__":
    """
    Fill in your server communication code here...

    example: 
    """

    coordinates = server('get_coordinates')
    
    """
    To test interactively, type: 
    ----------------------------
    python
    from assignment2 import *
    ----------------------------

    Then you might have a session along the lines of: 
    ------------------------------------------------
    coordinates = server('get_coordinates')
    coordinates = server('go_east',location=coordinates)
    coordinates
    ------------------------------------------------
    """
    
    pass

    
