
CoInductive Conat : Type := 
| cz : Conat
| cs : Conat -> Conat.  

CoFixpoint f (n : Conat) := cs (f (cs n)).

f  : Conat -> Conat
|| @c : Conat
\/
cs (f (cs c))
|| cs 
\/ 
f (cs c) 
