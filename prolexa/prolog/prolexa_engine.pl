%:- module(prolexa_engine,
%	[
%		prove_question/3,		% main question-answering engine
%		explain_question/3,		% extended version that constructs a proof tree
%		known_rule/2,			% test if a rule can be deduced from stored rules
%		all_rules/1,			% collect all stored rules
%		all_answers/2,			% everything that can be proved about a particular Proper Noun
%	]).

:- consult(library).


%%% Main question-answering engine adapted from nl_shell.pl %%%

prove_question(Query,SessionId,Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),     % create a list of all the rules and store them in RuleBase
	write_debug("prove3"),
	write_debug(Query),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		write_debug(Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
 	; prove_rb(not(Query),Rulebase) ->
		transform(not(Query),Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; Answer = 'Sorry, I don\'t think this is the case'
	).

% two-argument version that can be used in maplist/3 (see all_answers/2)
prove_question(Query,Answer):-
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase),
	write_debug("prove2"),
	write_debug(Query),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; prove_rb(not(Query),Rulebase) ->
		transform(not(Query),Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; Answer = "Sorry, I don\'t think this is the case"
	).

% finding all the facts associated with an proper noun
prove_exists(Query,Answer):-
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		Answer = Query
	; prove_rb(not(Query),Rulebase) ->
		transform(not(Query),Clauses),
		Answer = not(Query)
	; Answer = "Sorry, I don\'t think this is the case"
	).


%%% Extended version of prove_question/3 that constructs a proof tree %%%
explain_question(Query,SessionId,Answer):-
	write_debug('--------'),
	write_debug(Query),
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase,[],Proof) ->
		maplist(pstep2message,Proof,Msg),
		phrase(sentence1([(Query:-true)]),L),
		atomic_list_concat([therefore|L]," ",Last),
		append(Msg,[Last],Messages),
		atomic_list_concat(Messages," ; ",Answer)
	; prove_rb(not(Query),Rulebase,[],Proof) ->
		maplist(pstep2message,Proof,Msg),
		phrase(sentence1([(not(Query):-true)]),L),
		atomic_list_concat([therefore|L]," ",Last),
		append(Msg,[Last],Messages),
		atomic_list_concat(Messages," ; ",Answer)
 	;
		Answer = 'Sorry, I don\'t think this is the case'
	).


% convert proof step to message
pstep2message(p(_,Rule),Message):-
	rule2message(Rule,Message).

pstep2message(p(_,Rule),Message):-
	rule2message(Rule,Message).


pstep2message(n(Fact),Message):-
	rule2message([(Fact:-true)],FM),
	atomic_list_concat(['It is not known that',FM]," ",Message).


%%% test if a rule can be deduced from stored rules %%%
known_rule([Rule],SessionId):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
	try(
		(numbervars(Rule,0,_),
	     Rule=(H:-B),
	     add_body_to_rulebase(B,Rulebase,RB2),
	     prove_rb(H,RB2))).


add_body_to_rulebase((A,B),Rs0,Rs):-!,
	add_body_to_rulebase(A,Rs0,Rs1),
	add_body_to_rulebase(B,Rs1,Rs).
add_body_to_rulebase(A,Rs0,[[(A:-true)]|Rs0]).


%%% meta-interpreter that constructs proofs %%%

% 3d argument is accumulator for proofs

% base case
prove_rb(true,_Rulebase,P,P):-  !. %write_debug(" prove rb 1 "),

prove_rb((A,B),Rulebase,P0,P):-!,
	find_clause((A:-C),Rule,Rulebase),
	conj_append(C,B,D),
    prove_rb(D,Rulebase,[p((A,B),Rule)|P0],P).

prove_rb(A,Rulebase,P0,P):- %We have A :- true, tries to find A:-B then prove B :- true
    find_clause((A:-B),Rule,Rulebase),% write_debug(Rule),
	prove_rb(B,Rulebase,[p(A,Rule)|P0],P).


% prove_rb(A,Rulebase,P0,P):- %We have A :- true, tries to find A:-not(B) then prove not(B) :- true
%     find_clause((B:-not(A)),Rule,Rulebase), write_debug(Rule),  %works because (uniquely) A :- not(B) is equiv. to B :- not(A)
% 	prove_rb(not(B),Rulebase,[p(A,Rule)|P0],P).

% top-level version that ignores proof
prove_rb(Q,RB):-
	prove_rb(Q,RB,[],_P).			% calls back to prove_rb/4

%%% Utilities from nl_shell.pl %%%



find_clause(Clause,Rule,[Rule|_Rules]):-
	copy_term(Rule,[Clause]).	% do not instantiate Rule
find_clause(Clause,Rule,[_Rule|Rules]):-
	find_clause(Clause,Rule,Rules).

% transform instantiated, possibly conjunctive, query to list of clauses
transform((A,B),[(A:-true)|Rest]):-!,
    transform(B,Rest).
transform(A,[(A:-true)]).


%%% Two more commands: all_rules/1 and all_answers/2

% collect all stored rules
all_rules(Answer):-
	write_debug("all rules called"),
	findall(R,prolexa:stored_rule(_ID,R),Rules),
	maplist(rule2message,Rules,Messages),
	( Messages=[] -> Answer = "I know nothing"
	; write_debug('building message,'), otherwise -> atomic_list_concat(Messages,". ",Answer)
	).

% convert rule to sentence (string)
rule2message(Rule,Message):-
	phrase(sentence1(Rule),Sentence),
	atomics_to_string(Sentence," ",Message).


% collect everything that can be proved about a particular Proper Noun
all_answers(PN,Answer):-
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
	maplist(prove_question,Queries,Msg),
	delete(Msg,"Sorry, I don\'t think this is the case",Messages),

	% our additions ===================================
	maplist(prove_exists,Queries,Msg2),
	delete(Msg2,"Sorry, I don\'t think this is the case",Messages2),
	message_testing(Messages2, Clauses),
	write_debug(Clauses),
	% ==================================================

	( Messages=[] -> atomic_list_concat(['I know nothing about',PN],' ',Answer)
	; otherwise -> atomic_list_concat(Messages,".",Answer)
	).

% collect everything that can be proved about a particular Proper Noun
collect_facts(PN,New_rules):-
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
  write_debug(Queries),
	maplist(prove_exists,Queries,Msg2),
	delete(Msg2,"Sorry, I don\'t think this is the case",Messages2),
	%write_debug(Messages2),

	message_testing(Messages2, New_rules),
	write_debug(New_rules).

build_existential_rules(List, Pairs):-
  setof([(X:-Y)], (member(X, List), member(Y, List)), Matches),
  delete(Matches, [(X:-X)], Pairs).

message_testing(Messages, Clauses) :-
	write_debug("\nMessages: "),
	names(Names),
	write_debug(Names),
	write_debug(Messages),
	build_existential_rules(Messages, Clauses).

names(Names):-
	findall(Q,(pred(teacher,1,_),Q=..[teacher,PN]),Names).
	% findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries).
	% findall(Q,(proper_noun(s,PN),Q=..[PN]),Names).
	% setof(R, prolexa:stored_rule(_ID,R), InterimRules),
	% write_debug(InterimRules),
	% write_debug(member([(_A(PN):-true)], InterimRules)).
  % setof(PN, member(_A(PN):-true, InterimRules), Names).
