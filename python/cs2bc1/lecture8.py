#!/usr/bin/env python

# A magic inaccessible object meaning method failure
class Bottom:
    pass

# Examples of message passing

def makePerson(name):

    # This is how you make attributes / internal state
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
            return Bottom

    return aPerson


def runExample1():

    alice = makePerson("alice")
    jeff = makePerson("jeff")

    alice('say hello', caller=jeff)
    jeff('say hello', caller=alice)

    print "Name: "+alice('name')
    print "Name: "+jeff('name')

# Objects can have internal state
def runExample2():

    emmet = makePerson("emmet")
    jules = makePerson("jules")

    christa = makePerson("christa")
    janet = makePerson("janet")
    
    jules('have child', child=emmet)
    jules('list children')

    janet('have child', child=christa)
    janet('have child', child=emmet)
    janet('list children')

# Duck typing / Polymorphism
def makeDog():
    def aDog(message): 
        if message == 'bark':
            print "roof, roof!"
        elif message == 'run':
            print "see spot run..."
        else:
            return Bottom

    return aDog

def makeSeal():
    def aSeal(message): 
        if message == 'bark':
            print "arf, arf!"
        elif message == 'swim':
            print "splish... splash"
        else:
            return Bottom

    return aSeal

def causeMoonToRise(obj):
    print "\n"
    obj('bark')

def runExample3():
    fido = makeDog()
    floppy = makeSeal()

    causeMoonToRise(fido)
    causeMoonToRise(floppy)

# Inheritance Abstraction
def extend(child, parent):
    def anObj(message,**kwargs): 
        result = child(message,**kwargs)

        if result == Bottom:
            return parent(message,**kwargs)
        else:
            return result

    return anObj
        
def makePet(name):
    def pet(message): 
        if message == 'name':
            return name
        else:
            return Bottom

    return pet

def runExample4():
    dog = makeDog()
    pet = makePet('lassie')

    lassie = extend(pet,dog)

    print "Name: "+lassie('name')
    lassie('bark')

# Encapsulation
def makeSet(initial_contents):
    d = {'contents' : initial_contents}

    def aSet(message,obj):
        if message == 'has':
            return obj in d['contents']
        elif message == 'comprehension':
            result = []
            for elt in d['contents']:
                if obj(elt):
                    result.append(elt)
            return makeSet(result)

    return aSet
    
def runExample5():

    s = makeSet([1,2,3])
    print "2 in s? "
    print s('has',2)
    print "\n99 in s? "
    print s('has',99)
    
    p = lambda x: x > 1
    
    t = s('comprehension',p)
    print "\n\n1 in t? "
    print t('has',1)
    print "\n3 in t? "
    print t('has',3)


if __name__ == "__main__":
    print "\n\nExample 1: Message passing and instance construction\n\n"
    runExample1()

    print "\n\nExample 2: Side effects / State\n\n"
    runExample2()

    print "\n\nExample 3: Duck typing and Polymorphism\n\n"
    runExample3()

    print "\n\nExample 4: Inheritance abstraction\n\n"
    runExample4()
    
    print "\n\nExample 5: Encapsulation\n\n"
    runExample5()
