% Edited version of 8.1.1.pl with `explain(A,E0,[default((A:-B))|E])` removed
:-op(900,fy,not).

% explain(F,E) <- E explains F from rules and defaults
explain(F,E):-
    explain(F,[],E).

% meta-interpreter for rules and defaults
:- discontiguous explain/3.
explain(true,E,E):-!.
explain((A,B),E0,E):-!,
    explain(A,E0,E1),
    explain(B,E1,E).
explain(A,E0,E):-
    prove_e(A,E0,E).         % explain by rules only

% meta-interpreter for rules
prove_e(true,E,E):-!.
prove_e((A,B),E0,E):-!,
    prove_e(A,E0,E1),
    prove_e(B,E1,E).
prove_e(A,E0,[rule((A:-B))|E]):-
    rule((A:-B)),
    prove_e(B,E0,E).

% check contradiction against rules
contradiction(not A,E):-!,
    prove_e(A,E,_E1).
contradiction(A,E):-
    prove_e(not A,E,_E1).

explain(A,E0,[default(Name)|E]):-
    default(Name,(A:-B)),       % explain by default rule
    explain(B,E0,E),
    not contradiction(Name,E),  % default applicable
    not contradiction(A,E).     % A consistent with E

/** <examples>
?- explain(flies(dracula),E).
?- explain(not flies(dracula),E).
*/

% default(Name,Rule)
default(mammals_dont_fly(X),(not flies(X):-mammal(X))).
default(bats_fly(X),(flies(X):-bat(X))).
default(dead_things_dont_fly(X),(not flies(X):-dead(X))).
rule((mammal(X):-bat(X))).
rule((bat(dracula):-true)).
rule((dead(dracula):-true)).
% bats are flying mammals
rule((not mammals_dont_fly(X):-bat(X))).
% dead bats don't fly
rule((not bats_fly(X):-dead(X))).
