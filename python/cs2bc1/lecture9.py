#!/usr/bin/env python

## Natural language problem description

"""A customer can browse through the product catalog and add the items to a shopping cart. He can proceed to the checkout as long as his shopping cart is not empty. A customer is required to login to the system when proceeding to the checkout or create an account if one does not already exist.
The order will be charged to the credit card associated with customer's account.  The customer needs to provides his full name, email address, phone number, credit card and billing address details when creating an account.

A customer can login to the system to maintain his account information, such as changing phone number, address, and credit card details, or check the status of his orders.

Upon order receipt, the shop sales staff will process the order by charging the customer's credit card. Once the order has been charged, he will then mark the order as paid and pass the goods to a courier company for delivery to the customer. If any item ordered is out of stock then the order will be marked as on hold.

The courier company will pack the item with standard packaging unless the order is marked as gift in which case the items are packaged as gift items.

If an item arrives damaged, the customer can return it by registering it in the online shop. The courier company will collect the item from customer and the sales staff will refund the money for that item.

The Marketing staff are responsible for maintaining the product catalog. They can also setup the promotion item list and send promotion emails to customers."""

## The OO way
class Catalogue:
    
    def __init__(self,stock=None):
        if stock:
            self.stock = stock
        else: 
            self.stock = {'t-shirt' : 1,
                          'poster' : 2}

    def list_contents(self):
        return self.stock
            
    def restock(self,item,number):
        if item in self.stock:
            self.stock[item] += number
        else:
            self.stock[item] = number

    def destock(self,item,number):
        
        if item in self.stock and self.stock[item] > number:
            self.stock[item] -= number
            return True
        else:
            return False
            
class ShoppingCart:
    
    def __init__(self):
        self.shopping_cart = {}

    def add_item(self,item):
        if item in self.shopping_cart:
            self.shopping_cart[item] += 1
        else:
            self.shopping_cart[item] = 1

    def checkout(self):
        if len(self.shopping_cart) > 0:
            print "we will bill you now"
            "Code goes here...."
        else:
            print "You have nothing in your cart"

class Server:
    def __init__(self):
        self.registered = {}
        self.shopping_carts = {}

    def register(self,user,passwd):
        if user in self.registered:
            return False
        else:
            self.registered[user]=passwd
            self.shopping_carts[user] = ShoppingCart()
            return True

    def registered(self,user):
        return self.registered[user]
        
    def authorise(self,user,passwd):
        if user in self.registered:
            return self.registered[user] == passwd and self.shopping_carts[user]
        else:
            return False
        
class Customer:
    
    def __init__(self,catalogue,server):
        self.catalogue = catalogue
        self.server = server
        self.shopping_cart = None
    
    def browse(self):
        return self.catalogue.list_contents()

    def login(self,user,passwd):
        cart = self.server.authorise(user,passwd)
        if cart:
            self.shopping_cart = cart
            return True
        else:
            return False

    def register(self,user,passwd):
        return self.server.register(user,passwd)
    
    def logged_in(self):
        return self.shopping_cart
        
    def select(self,item):
        if self.logged_in():
            res = self.catalogue.destock(item,1)
            if res:
                self.shopping_cart.add(item)
                return True
            else:
                print "Out of stock"
                return False
        else:
            print "Not logged in"
            return False

if __name__ == "__main__":
    server = Server()
    catalogue = Catalogue()
    customer = Customer(catalogue,server)
    customer.register("me","pass")
    customer.login("me","pass")
    customer.browse()
    customer.select('t-shirt')
