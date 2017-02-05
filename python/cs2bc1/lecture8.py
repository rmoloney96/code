#!/usr/bin/env python

# Examples of message passing

def makePerson(name):
    d = {'children' : []}
    
    def aPerson(message,**kwargs):
        
        if message == 'name':
            return name

        elif message == 'say hello':
            if kwargs['caller']:
                print "Hello there " + kwargs['caller']('name')
            else:
                print "Hello world"

        elif message == 'have child':
            d['children'] += [kwargs['child']]

        elif message == 'list children':
            print "\nChildren: "
            for child in d['children']:
                print "\t" + child('name')

        else:
            print "Error: No such method"

    return aPerson


def runExample1():

    # Make instances of person
    alice = makePerson("alice")
    jeff = makePerson("jeff")

    alice('say hello', caller=jeff)
    jeff('say hello', caller=alice)

    print "Name: "+alice('name')
    print "Name: "+jeff('name')

def runExample2():

    # Objects can have internal state
    emmet = makePerson("emmet")
    jules = makePerson("jules")

    christa = makePerson("christa")
    janet = makePerson("janet")
    
    jules('have child', child=emmet)
    jules('list children')

    janet('have child', child=christa)
    janet('have child', child=emmet)
    janet('list children')

# Duck typing
def makeDog(message):
    if message = 'bark':
        print "roof, roof!"
    elif message = 'run':
        print "see spot run..."
    else:
        print "Error: No such method"
        
def makeSeal(message):
    if message = 'bark':
        print "arf, arf!"
    elif message = 'swim':
        print "splish... splash"
    else:
        print "Error: No such method"

def runExample3():
    fido = makeDog()
    floppy = makeSeal()

    
        
if __name__ == "__main__":
    print "\n\nExample 1: Message passing and instance construction\n\n"
    runExample1()

    print "\n\nExample 2: Side effects / State"
    runExample2()

    print "\n\nExample 3: "
    # runExample2()
    
    print "\n\n"
