happy(fido).
happy(harry).
happy(X) :- rich(X).
rich(harry).
pretty(alex).
cornish(matt).

proper_noun(s,tweety) --> [tweety].
proper_noun(s,peter) --> [peter].
proper_noun(s,subin) --> [subin].
proper_noun(s,pixie) --> [pixie].

%findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries).
% [a,b,c].

%If two empty lists return the unique items

dosomething(List1, List2) :- dosomething(List1, [], List2).

dosomething([], Final, Final).
dosomething([H|T], Final0, Final) :- append(H, Final0, Final), dosomething(T, Final, Final).

combs([],[]).
combs([H|T],[H|T2]) :-
    combs(T,T2).
combs([_|T],T2) :-
    combs(T,T2).

list_pairs(List1, List2, Pairs) :-
    setof((X,Y), (member(X, List1), member(Y, List2)), Pairs).

not_same(List, Pairs):-
    setof((X,Y), (member(X, List), member(Y, List)), Matches),
    delete(Matches, (X,X), Pairs).


%names(Names):- setof(R, prolexa:stored_rule(_ID,R), Names).

% collect everything that can be proved about a particular Proper Noun
collect_facts(PN,New_rules):-
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
  write_debug(Queries),
	maplist(prove_question,Queries,Msg2),
	delete(Msg2,"Sorry, I don\'t think this is the case",Messages2),
	%write_debug(Messages2),

	message_testing(Messages2, New_rules),
	write_debug(New_rules).

build_existential_rules(List, Pairs):-
    setof([(X:-Y)], (member(X, List), member(Y, List)), Matches),
    delete(Matches, [(X:-X)], Pairs).

message_testing(Messages, Clauses) :-
	write_debug("\nMessages: "),
	write_debug(Messages),
	build_existential_rules(Messages, Clauses).
