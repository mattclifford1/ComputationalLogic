%:- module(prolexa_engine,
%	[
%		prove_question/3,		% main question-answering engine
%		explain_question/3,		% extended version that constructs a proof tree
%		known_rule/2,			% test if a rule can be deduced from stored rules
%		all_rules/1,			% collect all stored rules
%		all_answers/2,			% everything that can be proved about a particular Proper Noun
%	]).

:- consult(library).
:- op(600, xfy, '=>').


% handle existential questions
prove_question_exists(Query,SessionId,Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),     % create a list of all the rules and store them in RuleBase
	transform(Query,ClausesP),
	(
		write_debug('Query'),
		write_debug(Query),
		write_debug('RuleBase'),
		write_debug(RuleBase),
    prove_rb_e(Query,Rulebase),!,        % it can be solved
    transform(Query,Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; Answer = 'Sorry, I don\'t think this is the case'
	).

%  here until copy_element_e is taken from https://too.simply-logical.space/src/text/3_part_iii/7.3.html
prove_rb_e(true,_Rulebase):-!.
prove_rb_e((A,B),Rulebase):-!,
    prove_rb_e(A,Rulebase),
    prove_rb_e(B,Rulebase).
prove_rb_e(A,Rulebase):-
    find_clause_e((A:-B),Rulebase),
    prove_rb_e(B,Rulebase).

% find applicable clause in rulebase
find_clause_e(Clause,[Rule|_Rules]):-
    copy_element_e(Clause,Rule).  % don't instantiate Rule
find_clause_e(Clause,[_Rule|Rules]):-
    find_clause_e(Clause,Rules).

copy_element_e(X,Ys):-
    member(X1,Ys),
    copy_term(X1,X).


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

clauses_get(Query,Answer):-
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		write_debug(Clauses),
		Answer = Clauses
	; prove_rb(not(Query),Rulebase) ->
		transform(not(Query),Clauses),
		Answer = Clauses
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

	% write_debug("\nNames from grammar:"),
	% proper_nouns(Names),
	% write_debug("\nENTERING RULE ASSERTION"),
	% general_rules(Names),

	findall(R,prolexa:stored_rule(_ID,R),Rules),
	write_debug('Rules'),
	write_debug(Rules),
	maplist(rule2message,Rules,Messages),
	( Messages=[] -> Answer = "I know nothing"
	; write_debug('building message,'), otherwise -> atomic_list_concat(Messages,". ",Answer)
	).

% convert rule to sentence (string)
rule2message(Rule,Message):-
	phrase(sentence1(Rule),Sentence),
	atomics_to_string(Sentence," ",Message).

% convert rule to sentence (string)
rule2components(Rule,General_rule):-
	phrase(sentence(Rule),Components_interim),
	phrase(sentence(General_rule), Components_interim).


% collect everything that can be proved about a particular Proper Noun
all_answers(PN,Answer):-
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
	maplist(prove_question,Queries,Msg),
	delete(Msg,"Sorry, I don\'t think this is the case",Messages),
	( Messages=[] -> atomic_list_concat(['I know nothing about',PN],' ',Answer)
	; otherwise -> atomic_list_concat(Messages,".",Answer)
	).

% collect everything that can be proved about a particular Proper Noun
facts_for_name(PN,New_rulebase):-
	write_debug("\nentered facts for name\n"),
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
	write_debug("\nfound queries\n"),
	write_debug(Queries),
	maplist(prove_question,Queries,Msg),
	delete(Msg,"Sorry, I don\'t think this is the case",Messages),
	write_debug("\n Messages"),
	write_debug(Messages),

	% our additions ===================================
	maplist(prove_exists,Queries,Msg2),
	delete(Msg2,"Sorry, I don\'t think this is the case",Messages2),
	message_testing(Messages2, Clauses),
	write_debug("\n CLAUSES:"),
	write_debug(Clauses),
	write_debug("\n Messages 2"),
	write_debug(Messages2),
	list_to_set(Clauses, Clauses_set),
	maplist(rule2components, Clauses_set, Exist_rules_set),
	write_debug("\n Exist_rules_set"),
	write_debug(Exist_rules_set),
	% safe_rules(Exist_rules_set, Exist_rules),
	write_debug("\nExistential rules: "),
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase_hard),
	write_debug("hard rulebase:"), write_debug(Rulebase_hard),
	append(Exist_rules_set, Rulebase_hard, New_rulebase),
	write_debug("\nnew rulebase:"), write_debug(New_rulebase),
	assert_rules(New_rulebase).



general_rules([]):- write_debug("Exit clause called").
general_rules([H|T]) :- write_debug(H), write_debug(T), facts_for_name(H, _), general_rules(T).

build_existential_rules(List, Pairs):-
  setof([(X:-Y)], (member(X, List), member(Y, List)), Matches),
  delete(Matches, [(X:-X)], Pairs).

message_testing(Messages, Clauses) :-
	write_debug("\nMessages in message testing: "),
	write_debug(Messages),
	build_existential_rules(Messages, Clauses).
%
% names(Names):-
% 	findall(Q,(pred(P,1,_),Q=..[P,PN]),Attributes),
% 	write_debug('\nAttributes:'),
% 	write_debug(Attributes),
% 	maplist(clauses_get,Attributes,Msg3),
% 	Names = [peter, subin, pixie, tweety],
% 	delete(Msg3,"Sorry, I don\'t think this is the case",Msg4),
% 	write_debug("MESSAGE 4"),
% 	write_debug(Msg4).

assert_rules([]).
assert_rules([H|T]) :- H= [(A :- B)],
 											 (
											 known_rule([(B:-A)],SessionId);
											 known_rule([(A:-B)],SessionId);
											 assertz(prolexa:stored_rule(SessionId,H))
											 ),
											 assert_rules(T).

% safe_rules(Exist_rules_2, Exist_rules),
safe_rules([], Safe_rules).
safe_rules([H|T], [L]) :- H= [(A :- B)],
											 (
											 known_rule([(B:-A)],SessionId), safe_rules(T, [L]);
											 known_rule([(A:-B)],SessionId), safe_rules(T, [L]);
											 safe_rules(T, [H|L])
											 ).



% call -- append_not_known(Exist_rules, Hard_rules).
% known_inlist -> checks if rule in Both_rules list

append_not_known(Exist_rules, [Both_rules]):-
	(
	known_inlist([(B:-A)],[Both_rules]), append_not_known(T, [L]);
	known_inlist([(A:-B)],[Both_rules]), append_not_known(T, [L]);
	append_not_known(T, [H|L])
	).
