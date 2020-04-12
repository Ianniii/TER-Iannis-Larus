%------------------------------------------------------------------------------
% File     : KRS164+1 : ILTP v1.1.2
% Domain   : Knowledge Representation (Semantic Web)
% Problem  : Two classes may have the same class extension
% Version  : Especial.
% English  : 

% Refs     : [Bec03] Bechhofer (2003), Email to G. Sutcliffe
%          : [TR+04] Tsarkov et al. (2004), Using Vampire to Reason with OW
% Source   : [Bec03]
% Names    : positive_equivalentClass-Manifest001 [Bec03]

% Status   : Theorem
% Rating   : 0.00 v3.1.0
%
% Status (intuit.) : Theorem
% Rating (intuit.) : 0.00 v1.1.0
%
% Syntax   : Number of formulae    :    8 (   4 unit)
%            Number of atoms       :   18 (   0 equality)
%            Maximal formula depth :    6 (   3 average)
%            Number of connectives :   14 (   4 ~  ;   0  |;   7  &)
%                                         (   3 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-1 arity)
%            Number of functors    :    2 (   2 constant; 0-0 arity)
%            Number of variables   :    5 (   0 singleton;   5 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : Sean Bechhofer says there are some errors in the encoding of
%            datatypes, so this problem may not be perfect. At least it's
%            still representative of the type of reasoning required for OWL.
%------------------------------------------------------------------------------
%----Thing and Nothing 
fof(axiom_0,axiom,
    ( ! [X] : 
        ( cowlThing(X)
        & ~ cowlNothing(X) ) )).

%----String and Integer disjoint 
fof(axiom_1,axiom,
    ( ! [X] : 
        ( xsd_string(X)
      <=> ~ xsd_integer(X) ) )).

%----Equality cCar
fof(axiom_2,axiom,
    ( ! [X] : 
        ( cCar(X)
      <=> cAutomobile(X) ) )).

%----iauto
fof(axiom_3,axiom,
    ( cAutomobile(iauto) )).

%----iauto
fof(axiom_4,axiom,
    ( cowlThing(iauto) )).

%----icar
fof(axiom_5,axiom,
    ( cCar(icar) )).

%----icar
fof(axiom_6,axiom,
    ( cowlThing(icar) )).

%----Thing and Nothing 
%----String and Integer disjoint 
%----iauto
%----iauto
%----icar
%----icar
fof(the_axiom,conjecture,
    ( ! [X] : 
        ( cowlThing(X)
        & ~ cowlNothing(X) )
    & ! [X] : 
        ( xsd_string(X)
      <=> ~ xsd_integer(X) )
    & cCar(iauto)
    & cowlThing(iauto)
    & cAutomobile(icar)
    & cowlThing(icar) )).

%------------------------------------------------------------------------------