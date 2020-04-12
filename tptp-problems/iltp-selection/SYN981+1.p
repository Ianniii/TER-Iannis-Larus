%--------------------------------------------------------------------------
% File     : SYN981+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Syntactic from Shults
% Version  : Especial.
% English  : 

% Refs     : [Shu04] Shults (2004), Email to G. Sutcliffe
% Source   : [Shu04]
% Names    :

% Status   : Theorem
% Rating   : 0.11 v3.1.0
%
% Status (intuit.) : Theorem
% Rating (intuit.) : 0.00 v1.1.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    6 (   0 equality)
%            Maximal formula depth :    5 (   5 average)
%            Number of connectives :    5 (   0 ~  ;   0  |;   1  &)
%                                         (   0 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-1 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    3 (   0 singleton;   1 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(prove_this,conjecture,
    ( ( ! [X] : 
          ( p(X)
         => q(X) )
      & ? [Y] : 
          ( q(Y)
         => r(Y) ) )
   => ? [Z] : 
        ( p(Z)
       => r(Z) ) )).

%--------------------------------------------------------------------------