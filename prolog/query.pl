:- module(query, [%% Give a class frame for a given class.
			  classFrame/3,
			  % Various class/entity queries 
			  allEntities/2, instanceClass/3,
			  %% Fill a given class frame with data.
			  fillClassFrame/5]).

:- use_module(utils).
:- use_module(library(http/http_log)).
:- use_module(library(semweb/rdf_db)).
:- use_module(library(semweb/rdf_label)).
:- use_module(library(semweb/rdf_persistency)).
:- use_module(datatypes).
:- use_module(tbox).
:- use_module(abox).
:- use_module(transactionGraph).
	     
% We should be creating stubs from the underlying graph
% which means we need some way to query it.

% It's quite possible all of these predicates should be replaced with a
% specialisation of a single graph fold predicate. 


/******************************************************

Structure of template description

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Frame grammar

KeyValPairs := a = b
Params := list keyValPairs
Restparams := [mincard=N, valuesFrom=Class] | [maxcard=N, valuesFrom=Class] | [card=N, valuesFrom=Class] | [hasValue=value] | [allValuesFrom=Class] | [someValuesFrom=Class]
Restriction := Restparams | true
Property := Restriction * Params
Frame := Op * list Frame | Property | Restriction
Op := and | or | xor
Error := [type=Reason] + Params
Reason := distortedFrame | ...

We have a predicate frame(Frame). which is true if the frame matches the frame grammar, 
and a predicate invalidFrame(Frame) which throws an exception of the frame grammar is 
violated. 

*******************************************************/
	  
propertyRestriction(true).
propertyRestriction(L) :-
	is_list(L),
	member(type=Type, L),
	member(Type,['and','or','not', 'xor']),
	member(operands=Ops),
	forall(propertyRestriction,Ops).
propertyRestriction(L) :-
	member(mincard=_,L),
	member(valuesFrom=_,L).
propertyRestriction(L) :-
	member(maxcard=_,L),
	member(valuesFrom=_,L).
propertyRestriction(L) :-
	member(card=_,L),
	member(valuesFrom=_,L).
propertyRestriction(L) :-
	member(hasValue=_,L).
propertyRestriction(L) :-
	member(allValuesFrom=_,L).
propertyRestriction(L) :-
	member(someValuesFrom=_,L).

prop(P) :-
	member(type=Type,P),
	member(Type, [objectProperty, datatypeProperty]),
	member(domain=Domain,P),
	member(range=Range,P),
	(member(frame=Frame,P) -> frame(Frame)
	 ; true),
	(member(restriction=R,P) -> propertyRestriction(R)
	 ; true).

propertyFrame(Ps) :- forall(prop,Ps).

logicalFrame(F) :-
	member(type=Type, F),
	member(Type,['and','or','not', 'xor']),
	forall(operands=Ops),
	forall(frame, Ops).

frame(F) :- logicalFrame(F).
frame(F) :- propertyFrame(F).

% Type at which to "clip" graphs to form trees
entity(Class,Schema) :-
	subsumptionOf(Class, 'http://dacura.cs.tcd.ie/ontology/utv#Entity', Schema). 

allEntities(Schema,AE) :-
	uniqueSolns(E,query:entity(E,Schema),AE).

addMostSpecificProperty(Schema,P,PList,Rp) :-
	% write('P: '),writeq(P),nl,
	member(Q,PList), % write('Q: '),writeq(Q),nl,
	(subsumptionPropertiesOf(P,Q,Schema) *-> select(Q,PList,PListp), Rp=[P|PListp], % write('P < Q'),nl
	 ; (subsumptionPropertiesOf(Q,P,Schema) *-> Rp=PList, % write('Q < P'), nl
		; Rp=[P|PList])), !.
addMostSpecificProperty(Schema,P,PList,[P|PList]).

mostSpecificProperties(Schema,Properties,SpecificProperties) :-
	foldl(addMostSpecificProperty(Schema),Properties,[],SpecificProperties). 

classProperties(Class, Schema, PropertiesPrime) :-
	uniqueSolns(P,tbox:anyDomain(P,Class,Schema),Properties),
	mostSpecificProperties(Schema,Properties,PropertiesPrime).

:- rdf_meta hasFormula(r,o).
hasFormula(Class,Schema) :-
	subClassOf(Class,_,Schema)
	; intersectionOf(Class,_,Schema)
	; unionOf(Class,_,Schema)
	; disjointUnionOf(Class,_,Schema).

:- rdf_meta restrictionType(r,t,?).
restrictionType(CR,restriction([uri=CR,property=OP,someValuesFrom=C]),Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:someValuesFrom,C,Schema).
restrictionType(CR,restriction([uri=CR,property=OP,allValuesFrom=C]),Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:allValuesFrom,C,Schema).
restrictionType(CR,restriction([uri=CR,property=OP,minCardinality=N]),Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:minCardinality,literal(type(xsd:nonNegativeInteger, CardStr)),Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,maxCardinality=N]),Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:maxCardinality,literal(type(xsd:nonNegativeInteger, CardStr)),Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,cardinality=N]),Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:cardinality,literal(type(xsd:nonNegativeInteger, CardStr)),Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,minQualifiedCardinality=N,onClass=C]), Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:minQualifiedCardinality,literal(type(xsd:nonNegativeInteger, CardStr)),Schema),
	xrdf(CR,owl:onClass,C,Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,maxQualifiedCardinality=N,onClass=C]), Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:maxQualifiedCardinality,literal(type(xsd:nonNegativeInteger,CardStr)),Schema),
	xrdf(CR,owl:onClass,C,Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,qualifiedCardinality=N,onClass=C]), Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:qualifiedCardinality,literal(type(xsd:nonNegativeInteger,CardStr)),Schema),
	xrdf(CR,owl:onClass,C,Schema),
	atom_number(CardStr,N).
restrictionType(CR,restriction([uri=CR,property=OP,hasValue=V]), Schema) :-
	xrdf(CR,owl:onProperty,OP,Schema),
	xrdf(CR,owl:hasValue,V,Schema).

%% classAssertion(?Schema:Atom, +Class:Atom, -Formula:Term) is nondet
%  
% Get one solution of the OWL class assertions
%
% @param Schema Atom idntifying the current schema graph.
% @param Class Atom URI identifier of rfds or owl Class.
% @param Formula Term describing the class relationships.
:- rdf_meta classAssertion(o,r,t).
classAssertion(Schema, Class, (Class<SuperFormula)) :-
	%class(Class,Schema),
	subClassOf(Class,Y,Schema),
	classFormula(Schema, Y, SuperFormula).
classAssertion(Schema, Class, (Class=and(Solns))) :-
	%class(Class,Schema),
	setof(Sol,Y^(tbox:intersectionOf(Class,Y,Schema),
				 query:classFormula(Schema,Y,Sol)),
		  Solns).
classAssertion(Schema,Class,(Class=or(Solns))) :-
	%class(Class,Schema),
	setof(Sol,Y^(tbox:unionOf(Class,Y,Schema),
				 query:classFormula(Schema,Y,Sol)),
		  Solns).
classAssertion(Schema,Class,(Class=xor(Solns))) :-
    %class(Class,Schema),
    setof(Sol,Y^(tbox:disjointUnionOf(Class,Y,Schema),
				 query:classFormula(Schema,Y,Sol)),
		  Solns).
classAssertion(Schema,Class,(Class=oneOf(OneList))) :-
	oneOfList(Class,OneList,Schema).
classAssertion(Schema,Class,RType) :-
	restriction(Class,Schema),
	restrictionType(Class,RType,Schema).
classAssertion(Schema,Class,class(Class)) :-
	class(Class,Schema),
    \+ restriction(Class,Schema),
    \+ hasFormula(Class,Schema).

%% classFormula(?Schema:Atom, +Class:Atom, -Formula:Term) is nondet
%  
% Create a formula describing the manner in which the class is
% defined.
%
% @param Schema Atom idntifying the current schema graph.
% @param Class Atom URI identifier of rfds or owl Class.
% @param Formula Term describing the class relationships.
classFormula(Schema,Class,F) :-
	setof(Sol,classAssertion(Schema,Class,Sol), Solns),
	([F]=Solns -> true
	 ; F=(Class=and(Solns))).

maybeLabel(C,Schema,[label=L]) :-
    label(C,L,Schema), !.
maybeLabel(_,_,[]).

:- rdf_meta propertyFrame(o,o,r,t).
propertyFrame(Schema,C,P,property(restriction(true),[type=objectProperty,property=P,
													 domain=C,
													 range=R,
													 frame=F|Label])) :-
    maybeLabel(P,Schema,Label),
    mostSpecificRange(P,R,Schema),
    class(R,Schema),
	\+ entity(R,Schema),
	classFrame(R,Schema,F), !.
propertyFrame(Schema,C,P,property(restriction(true),[type=objectProperty,property=P,
													 domain=C,
													 range=R,
													 frame=[type=entity,class=R|RLabel]|Label])) :-
    maybeLabel(P,Schema,Label),
    mostSpecificRange(P,R,Schema),
    class(R,Schema),
    entity(R,Schema),
	maybeLabel(R,Schema,RLabel),!.
propertyFrame(Schema,C,P,property(restriction(true),[type=datatypeProperty,property=P,
													 domain=C,
													 range=R|Label])) :-
    maybeLabel(P,Schema,Label),
    mostSpecificRange(P,R,Schema),
    datatype(R,Schema), !.
propertyFrame(_,C,P,error([type=distortedFrame, property=P,
						   domain=C,
						   message='The property has insufficient schema information'])).

disjointUnionFrames(Frames,xor(Frames)).

addProperty(Schema,P,Frame,Rp) :-
	write('P: '),writeq(P),nl,
	member(Q,Frame), write('Q: '),writeq(Q),nl,
	member(property=Prop, P),
	member(property=Prop, Q),
	member(domain=D, P),write('D: '),writeq(D),nl,
	member(domain=E, Q),write('E: '),writeq(D),nl,
	(subsumptionOf(D,E,Schema) *-> Rp=Frame, write('D < E'),nl
	 ; (subsumptionOf(E,D,Schema) *-> select(Q,Frame,Framep), Rp=[P|Framep], write('E < D'),nl
		; Rp=[P|Frame],nl,writeq('D <> E'))), !.
addProperty(Schema,P,Frame,[P|Frame]) :- write('P <prop> Q'), nl.
	
	
unionPropertyFrame(Schema,FrameA,FrameB,FrameC) :-
	foldl(addProperty(Schema),FrameA,FrameB,FrameC).

unionFramesTest(Schema,Frames,Frame) :-
    foldl(unionPropertyFrame(Schema),Frames,[],Frame). 

unionFrames(Frames,or(Frames)).

intersectRestriction(true,S,S) :- !.
intersectRestriction(S,true,S) :- !.
intersectRestriction(restriction(S),restriction(R),restriction(and([S,R]))). 	

%%% DDD fix intersection restrictions
intersectionProperty(property(R,P),property(S,Q),property(T,P)) :-
	member(property=Prop,P), %% Too strong - should be subsumption
	member(property=Prop,Q),
	intersectRestriction(R,S,T).
intersectionProperty(restriction(R),property(S,P),property(T,P)) :-
	member(property=Prop,P), %% Too strong - should be subsumption
	member(property=Prop,R),
	intersectRestriction(R,S,T).
intersectionProperty(propery(R,P),restriction(S),property(T,P)) :-
	member(property=Prop,P), %% Too strong - should be subsumption
	member(property=Prop,S),
	intersectRestriction(R,S,T).

:- rdf_meta supProperty(r,r,r).
infimumProperty(PropA,PropB,Schema,PropA) :-
    strictSubsumptionPropertiesOf(PropA,PropB,Schema).
infimumProperty(PropA,PropB,Schema,PropB) :-
    strictSubsumptionPropertiesOf(PropB,PropA,Schema).
infimumProperty(PropA,PropA,_,PropA).

renameProperty(R,PropertyOld,PropertyNew,[property=PropertyNew|Rp]) :-
    select(property=PropertyOld,R,Rp).

intersectionFrame(Schema,xor(Frames),A,xor(NewFrames)) :-
	maplist(intersectionFrame(Schema,A),Frames,NewFrames), !.
intersectionFrame(Schema,A,xor(Frames),xor(NewFrames)) :-
	maplist(intersectionFrame(Schema,A),Frames,NewFrames), !.
intersectionFrame(Schema,or(R),A,or(F)) :-
	maplist(intersectionFrame(Schema,A),R,F), !.
intersectionFrame(Schema,A,or(R),or(F)) :-
	maplist(intersectionFrame(Schema,A),R,F), !.
intersectionFrame(_Schema,_A,oneof(L),oneof(L)) :- !.
    % ???
    % probably need to make a list of restriction objects where elt =  or something?
intersectionFrame(_,FrameA,[],FrameA) :- !.
intersectionFrame(_,[],FrameB,FrameB) :- !.
intersectionFrame(Schema,[R|FrameA],FrameB,[T|FrameC]) :-
	is_list(FrameB),
    member(property=PropertyA,R),
    member(S,FrameB),
    member(property=PropertyB,S),
    infimumProperty(PropertyA,PropertyB,Schema,PropertyC),
    renameProperty(R,PropertyA,PropertyC,Rp),
    renameProperty(S,PropertyB,PropertyC,Sp),
    intersectionProperty(Rp,Sp,T),
    select(S,FrameB,FrameB2) -> 
	intersectionFrame(Schema,FrameA,FrameB2,FrameC), !.
intersectionFrame(Schema,[R|FrameA],FrameB,[R|FrameC]) :-
	is_list(FrameB),
    member(property=Property,R),
    member(S,FrameB),
    \+ member(property=Property,S) -> 
	intersectionFrame(Schema,FrameA,FrameB,FrameC), !.
%%intersectionFrame(Schema,[[F]|R],FrameB,[X]) :-
	

intersectionFrames(Schema,[A|Frames],Frame) :-
    foldl(intersectionFrame(Schema),Frames,A,Frame).

% Builds a frame from a class formula
:- rdf_meta classFrame(+,t,t,t).
traverseClassFormula(_,_,class('http://www.w3.org/2002/07/owl#Thing'),
					 [type=thing,class='http://www.w3.org/2002/07/owl#Thing']) :- !.
traverseClassFormula(Schema,Properties,class(C),properties(Frame)) :-
    classProperties(C,Schema,Properties2),
    union(Properties,Properties2,Properties3),
    maplist(propertyFrame(Schema,C),Properties3,Frame), !.
traverseClassFormula(Schema,Properties,C<D,Frame) :-
    classProperties(C,Schema,Properties2),
    union(Properties,Properties2,Properties3),
	maplist(propertyFrame(Schema,C),Properties3,Frame1),
    traverseClassFormula(Schema,Properties3,D,Frame2),
	intersectionFrames(Schema,[properties(Frame1),Frame2],Frame), !.
traverseClassFormula(Schema,Properties,C=xor(L),Frame) :-
    classProperties(C,Schema,Properties2),
    union(Properties,Properties2,Properties3),
	maplist(propertyFrame(Schema,C),Properties3,Frame1),
    maplist(traverseClassFormula(Schema,Properties3),L,Frames),
    disjointUnionFrames(Frames,Frame2),
	intersectionFrames(Schema,[Frame1,Frame2],Frame), !.
traverseClassFormula(Schema,Properties,C=and(L),Frame) :-
    classProperties(C,Schema,Properties2),
    union(Properties,Properties2,Properties3),
	maplist(propertyFrame(Schema,C),Properties3,Frame1),		
    maplist(traverseClassFormula(Schema,Properties3),L,Frames),
	writeq(Frames),
    intersectionFrames(Schema,[Frame1|Frames],Frame), !.
traverseClassFormula(Schema,Properties,C=or(L),Frame) :-
    classProperties(C,Schema,Properties2),
    union(Properties,Properties2,Properties3),
	maplist(propertyFrame(Schema,C),Properties3,Frame1),
    maplist(traverseClassFormula(Schema,Properties3),L,Frames),
    unionFrames(Frames,Frame2),
	intersectionFrames(Schema,[Frame1,Frame2],Frame), !.
traverseClassFormula(Schema,Properties,C=oneOf(OneList), Frame) :-
	classProperties(C,Schema,Properties2),
	union(Properties, Properties2, Properties3),
	maplist(propertyFrame(Schema,C),Properties3,Frame1),
	Frame2=oneOf(OneList),
	intersectionFrames(Schema,[Frame1,Frame2],Frame), !.
traverseClassFormula(_,_,restriction(L),restriction(L)) :- !.
traverseClassFormula(_,Properties,F,FailureFrame) :-
	interpolate([F],Msg),
	FailureFrame=[type=failure, message='mangled frame',
				  formula=Msg, properties=Properties], !.
    
:- rdf_meta classFrame(r,o,t).
classFrame(Class, Schema, Frame) :-
	classFormula(Schema,Class,Formula)
	-> traverseClassFormula(Schema, [], Formula, Frame)
	; Frame = [type=failure, message='No Class Formula!', class=Class].

%% No longer checking about foundedness 
%%
%% classFrame(Class, Schema, Frame) :-
%%     % No reasons [] for it to be not well founded...
%%     notWellFoundedFrame(Class, Schema, [])
%% 	-> (classFormula(Schema,Class,Formula)
%% 		-> traverseClassFormula(Schema, [], Formula, Frame)
%% 		; Frame = [type=failure, message='No Class Formula!', class=Class])
%%     ; Frame = [type=failure, message='Not well founded!', class=Class].

% This is a graph search using all possible property edges from classes.
% the "wellFoundedFrameHelper" takes an assoc
% * returns false if it finds a cycle
% * stops if it finds an "entity" or dataTypeProperty
%
/* Positively defined.
wellFoundedFrameHelper(Class,Schema,S1) :-
    get_assoc(Class, S1, true) ->
	fail
    ; (classProperties(Class,Schema,Properties) -> 
	   put_assoc(Class,S1,true,S2),
	   exclude(lambda(Pe,query:datatypeProperty(Pe,Schema)), Properties, ObjectProperties),
	   maplist(lambda(Pm,R,tbox:range(Pm,R,Schema)), ObjectProperties,Classes),
	   exclude(lambda(CE,query:entity(CE,Schema)),Classes, Clipped),
	   maplist(lambda(C, query:wellFoundedFrameHelper(C, Schema, S2)), Clipped)
       ; true).

:- rdf_meta wellFoundedFrame(r,o).
wellFoundedFrame(Class,Schema) :-
    empty_assoc(S), 
    wellFoundedFrameHelper(Class, Schema, S). 
*/

% This is a graph search using all possible property edges from classes.
% the "NotWellFoundedFrameHelper" takes an assoc list
% * returns a "Reason" if it finds a cycle, including the trail between classes.
% * stops if it finds an "entity" or dataTypeProperty
notWellFoundedFrameHelper(Class,Schema,S1,Trail,Reasons) :-
    get_assoc(Class, S1, true) ->
	interpolate(['There is a cycle in the frame to a class ',Class,
		     ' which is not an entity.'],
		    Message),
	reverse([Class|Trail],Cycle),
	Reasons = [['rdf:type'='FrameCycle',
		    bestPractice=literal(type('xsd:boolean', true)),
		    message=Message,
		    class=Class,
		    cycle=Cycle]]
    ; (classProperties(Class,Schema,Properties) -> 
	   put_assoc(Class,S1,true,S2),
	   exclude(lambda(Pe,query:datatypeProperty(Pe,Schema)), Properties, ObjectProperties),
	   maplist(lambda(Pm,target(Pm,R),tbox:range(Pm,R,Schema)), ObjectProperties,TargetClasses),
	   exclude(lambda(target(_,CE),query:entity(CE,Schema)), TargetClasses, Clipped),
	   maplist(lambda(target(Px,C), Rs, query:notWellFoundedFrameHelper(C, Schema, S2, [Px, Class|Trail], Rs)), Clipped, ReasonsList),
	   flatten(ReasonsList, Reasons)
       ; Reasons = []).

% notWellFoundedFrame checks to see if there are cycles in the graph without
% dacura:Entity demarcations which "clip" the graph.
% * THIS IS NOT A PREDICATE - it always succeeds with a list of reasons of failure
%   or an empty list for success.

:- rdf_meta notWellFoundedFrame(r,o,t).
notWellFoundedFrame(Class,Schema,Reasons) :-
    empty_assoc(S),
    notWellFoundedFrameHelper(Class,Schema,S,[],Reasons). 

fillClassFrame(_,_,_,[],[]) :- !.
fillClassFrame(Elt,Instance,Schema,[P|Rest],[[value=V,frame=Filled|Pp]|F]) :-
    member(type=objectProperty, P), !,
    member(property=Prop, P),
    inferredEdge(Elt, Prop, V, Instance, Schema),
    select(frame=Frame,P,Pp),
    fillClassFrame(V,Instance,Schema,Frame,Filled),
    fillClassFrame(Elt,Instance,Schema,Rest,F).
fillClassFrame(Elt,Instance,Schema,[P|Rest],[[value=V|P]|F]) :-
    member(type=datatypeProperty, P), !,
    member(property=Prop, P),
    inferredEdge(Elt, Prop, V, Instance, Schema),
    fillClassFrame(Elt,Instance,Schema,Rest,F).
fillClassFrame(Elt,Instance,Schema,[C|Rest],[[type=choice,frames=Fsp]|F]) :-
    member(type=choice, C), !,
    member(frames=Fs, C),
    maplist(fillClassFrame(Elt,Instance,Schema),Fs,Fsp),
    fillClassFrame(Elt,Instance,Schema,Rest,F).
fillClassFrame(_,_,_,F,F) :-
    member(type=entity, F), !.
