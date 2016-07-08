import Data.List 

map2 :: (s -> t) -> [s] -> [t]
map2 f [] = []
map2 f [x] = [f x]
map2 f (x : y : zs) = f x : f y : map2 f zs

nats :: [Integer]       
nats = 0 : map (1+) nats

nats2 :: [Integer]       
nats2 = 0 : map2 (1+) nats2      
