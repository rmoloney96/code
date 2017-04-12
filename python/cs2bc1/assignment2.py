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
           'items' : ['sword of damocles']},
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
            hsh.update(str(elt).encode('utf-8'))
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
        hsh.update(str(record).encode('utf-8'))
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
            hsh.update(str(new_record).encode('utf-8'))
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
            hsh.update(str(new_record).encode('utf-8'))
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
            hsh.update(str(new_record).encode('utf-8'))
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
            hsh.update(str(new_record).encode('utf-8'))
            new_record['location'] = hsh.hexdigest()
            return new_record
        else:
            return {'error' : "Out of bounds",
                    'msg' : "You have fallen off the edge of the world and have died."}
    elif request == 'pick_up':
        record = get_location(location)
        items = record['items']
        if len(items) > 0:
            item = items[0]
            hsh = hashlib.md5()
            hsh.update(item.encode('utf-8'))
            return hsh.hexdigest()
        else:
            return {'error' : "Nothing here",
                    'msg' : "There is nothing here to pick up"}
    elif request == 'slice' :
        hsh = hashlib.md5()
        hsh.update('gordian knot'.encode('utf-8'))
        a = hsh.hexdigest()
        hsh = hashlib.md5()
        hsh.update('sword of damocles'.encode('utf-8'))
        b = hsh.hexdigest()
        if (a in items and b in items):
            return {'success' : "Congragulations",
                    'msg' : "One way or another, you have successfully sliced the Gordian knot"}
        else:
            return {'error' : "incomplete",
                    'msg' : "You don't have all the necessary items"}
    else:
        return {'error' : "unrecognised request",
                'msg' : "The request: " + str(request) + " is not recognised."}


if __name__ == "__main__":
    """
    Fill in your server communication code here...
    
    coordinates = server('get_coordinates')
    new_coordinates = server('go_east', location=coordinates)
    coordinates = server('get_coordinates')
    sword = server('pick_up', location=coordinates)
    coordinates = server('get_coordinates')
    new_coordinates = server('go_west', location=coordinates)
    coordinates = server('get_coordinates')
    new_coordinates = server('go_north', location=coordinates)
    coordinates = server('get_coordinates')
    new_coordinates = server('go_north', location=coordinates)
    coordinates = server('get_coordinates')
    new_coordinates = server('go_east', location=coordinates)
    coordinates = server('get_coordinates')
    new_coordinates = server('go_east', location=coordinates)
    coordinates = server('get_coordinates')
    knot = server('pick_up', location=coordinates)
    coordinates = server('get_coordinates')
    success = server('slice', items=[sword,knot])
    
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
    print(coordinates)
    ------------------------------------------------
    """
    
    pass

    
