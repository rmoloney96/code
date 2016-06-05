propertyRestriction(true).
propertyRestriction(L) :-
	is_list(L),
	member(type=Type, L),
	member(Type,['and','or','not', 'xor']),
	member(operands=Ops),
	forall(propertyRestriction,Ops).

prop(P,M) :-
    \+ member(type=Type,P)
	-> M = [msg='No Property Type',record=P, predicate=notProp]
	; \+ member(Type, [objectProperty, datatypeProperty])
	  -> M = [msg='Not an objectProperty or datatypeProperty', record=P, predicate=notProp]
	; member(frame=Frame,P),
	  -> notFrame(Frame,M),
	; member(restriction=R,P)
	  -> notPopertyRestrictionR(R,M). 
