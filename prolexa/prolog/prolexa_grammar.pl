%%% Definite Clause Grammer for prolexa utterances %%%

utterance(C) --> sentence(C).
utterance(C) --> question(C).
utterance(C) --> command(C).

:- op(600, xfy, '=>').


%%% lexicon, driven by predicates %%%

adjective(_,M)		--> [Adj],    {pred2gr(_P,1,a/Adj, M)}.
noun(s,M)			--> [Noun],   {pred2gr(_P,1,n/Noun,M)}.
noun(p,M)			--> [Noun_p], {pred2gr(_P,1,n/Noun,M),noun_s2p(Noun,Noun_p)}.
iverb(s,M)			--> [Verb_s], {pred2gr(_P,1,v/Verb,M),verb_p2s(Verb,Verb_s)}.
iverb(p,M)			--> [Verb],   {pred2gr(_P,1,v/Verb,M)}.

% unary predicates for adjectives, nouns and verbs
pred(human,   1,[a/human,n/human]).
pred(mortal,  1,[a/mortal,n/mortal]).
pred(man,     1,[a/male,n/man]).
pred(woman,   1,[a/female,n/woman]).
pred(married, 1,[a/married]).
pred(bachelor,1,[n/bachelor]).
pred(mammal,  1,[n/mammal]).
pred(bird,    1,[n/bird]).
pred(bat,     1,[n/bat]).
pred(penguin, 1,[n/penguin]).
pred(sparrow, 1,[n/sparrow]).
pred(fly,     1,[v/fly]).
pred(sing,     1,[v/sing]).
pred(happy,     1,[a/happy]).
pred(teacher, 1 ,[n/teacher]).
pred(student, 1, [n/student]).

pred2gr(P,1,C/W,X=>Lit):-
	pred(P,1,L),
	member(C/W,L),
	Lit=..[P,X].

noun_s2p(Noun_s,Noun_p):-
	( Noun_s=woman -> Noun_p=women
	; Noun_s=man -> Noun_p=men
	; atom_concat(Noun_s,s,Noun_p)
	).

verb_p2s(Verb_p,Verb_s):-
	( Verb_p=fly -> Verb_s=flies
	; 	atom_concat(Verb_p,s,Verb_s)
	).


%%% sentences %%%

sentence(C) --> sword,sentence1(C).

sword --> [].
sword --> [that].

% most of this follows Simply Logical, Chapter 7


sentence1(C) --> determiner(N,M1,M2,C),noun(N,M1),verb_phrase(N,M2).%, [sent1].
sentence1([(L:-true)]) --> proper_noun(N,X),verb_phrase(N,X=>L).%, [sent2].


%sentence1(C) --> verb_phrase(N,M1), determiner(N,M1,M2,C), noun(N,M2).%, [sent1].

sentence1(C) --> reverse_verb_phrase(N,M1), determiner_reverse(N,M1,M2,C),  noun(N,M2).%, [sent1].

sentence1(C) --> determiner_neg(N,M1,M2,C), noun(N,M1), neg_verb_phrase(N,M2).%, [sent1].
sentence1(C) --> determiner_neg_double(N,M1,M2,C), noun(N,M1), double_verb_phrase(N,M2).%, [sent1].
sentence1([(not(L):-true)]) --> proper_noun(N,X),neg_verb_phrase(N,X=>L).%, [sent3].


% example "pixie is not red"

%sentence1([(not(M1):-not(M2))]) --> determiner(N,M1,M2,[(M1:-M2)]), noun(N,M1), neg_verb_phrase(N,M2).

% example "pixels are red, blue or green"


verb_phrase(s,M) --> [is],property(s,M).
verb_phrase(p,M) --> [are],property(p,M).
verb_phrase(p,M) --> [or],property(p,M).
verb_phrase(N,M) --> iverb(N,M).

neg_verb_phrase(s,M) --> [is, not],property(s,M).
neg_verb_phrase(p,M) --> [are, not],property(p,M).
neg_verb_phrase(p,M) --> [or, not], property(p,M).
neg_verb_phrase(N,M) --> [doesnt], iverb(N,M).

reverse_verb_phrase(s,M) --> [if],property(s,M).
reverse_verb_phrase(p,M) --> [if],property(p,M).

double_verb_phrase(s,M) --> [then, not],property(s,M).
double_verb_phrase(p,M) --> [then, not],property(p,M).
double_verb_phrase(N,M) --> [doesnt], iverb(N,M).

property(N,M) --> adjective(N,M).
property(s,M) --> [a],noun(s,M).
property(p,M) --> noun(p,M).

determiner(s,X=>B,X=>H,[(H:-B)]) --> [every].
determiner(p,X=>B,X=>H,[(H:-B)]) --> [all].
% existential skolem
determiner(p,sk=>H1,sk=>H2,[(H1:-true),(H2:-true)]) --> [some].

determiner_reverse(s,X=>B,X=>H,[(H:-B)]) --> [then].
determiner_reverse(p,X=>B,X=>H,[(H:-B)]) --> [then].

determiner_neg_double(s,X=>B,X=>H,[(not(H):-not(B))]) --> [if, not].
determiner_neg_double(p,X=>B,X=>H,[(not(H):-not(B))]) --> [if, not].

determiner_neg_double(s,X=>H,X=>B,[(not(H):-not(B))]) --> [if, not].
determiner_neg_double(p,X=>H,X=>B,[(not(H):-not(B))]) --> [if, not].

determiner_neg(s,X=>H,X=>B,[(H:-not(B))]) --> [every].
determiner_neg(p,X=>H,X=>B,[(H:-not(B))]) --> [all].

determiner_neg(s,X=>B,X=>H,[(not(H):-B)]) --> [every].
determiner_neg(p,X=>B,X=>H,[(not(H):-B)]) --> [all].

% neg_determiner(s,X=>not(B),X=>not(H),[(not(H):-not(B))]) --> [every].

%determiner(p,X=>B,X=>H,[(H:-B)]) --> [].
%determiner(p, sk=>H1, sk=>H2, [(H1:-true),(H2 :- true)]) -->[some].

proper_noun(s,tweety) --> [tweety].
proper_noun(s,peter) --> [peter].
proper_noun(s,subin) --> [subin].
proper_noun(s,pixie) --> [pixie].


%%% questions %%%

question(Q) --> qword,question1(Q).

qword --> [].
%qword --> [if].
%qword --> [whether].

question1(Q) --> [who],verb_phrase(s,_X=>Q).
question1(not(Q)) --> [who],neg_verb_phrase(s,_X=>Q).

question1(Q) --> [is], proper_noun(N,X),property(N,X=>Q).
question1(not(Q)) --> [is], proper_noun(N,X), [not], property(N,X=>Q).
question1(Q) --> [does],proper_noun(_,X),verb_phrase(_,X=>Q).
question1(not(Q)) --> [does],proper_noun(_,X),neg_verb_phrase(_,X=>Q).
%question1((Q1,Q2)) --> [are,some],noun(p,sk=>Q1),
%					  property(p,sk=>Q2).

%%% questions exists with skolem constants %%%
question_e(Q) --> qword,question1_e(Q).
question1_e((Q1,Q2)) --> [are,some],noun(p,sk=>Q1),property(p,sk=>Q2). % with skolem
% negative version
% question1_e((Q1,not(Q2))) --> [are,some],noun(p,sk=>Q1), [not], property(p,sk=>Q2). % with skolem

%%% commands %%%

% These DCG rules have the form command(g(Goal,Answer)) --> <sentence>
% The idea is that if :-phrase(command(g(Goal,Answer)),UtteranceList). succeeds,
% it will instantiate Goal; if :-call(Goal). succeeds, it will instantiate Answer.
% See case C. in prolexa.pl
% Example:
%	command(g(random_fact(Fact),Fact)) --> [tell,me,anything].
% means that "tell me anything" will trigger the goal random_fact(Fact),
% which will generate a random fact as output for prolexa.

command(g(retractall(prolexa:stored_rule(_,C)),"I erased it from my memory")) --> forget,sentence(C).
command(g(retractall(prolexa:stored_rule(_,_)),"I am a blank slate")) --> forgetall.
command(g(all_rules(Answer),Answer)) --> kbdump.
command(g(all_answers(PN,Answer),Answer)) --> tellmeabout,proper_noun(s,PN).

command(g(explain_question(Q,_,Answer),Answer)) --> [explain,why],sentence1([(Q:-true)]).
command(g(explain_question(not(Q),_,Answer),Answer)) --> [explain,why],sentence1([(not(Q):-true)]).

command(g(explain_question(Q,_,Answer),Answer)) --> [explain,why],sentence1([(not(Q):-true)]).


command(g(random_fact(Fact),Fact)) --> getanewfact.
%command(g(pf(A),A)) --> peterflach.
%command(g(iai(A),A)) --> what.
command(g(rr(A),A)) --> thanks.

% The special form
%	command(g(true,<response>)) --> <sentence>.
% maps specific input sentences to specific responses.

command(g(true,"I can do a little bit of logical reasoning. You can talk with me about humans and birds.")) --> [what,can,you,do,for,me,minerva].
%command(g(true,"Your middle name is Adriaan")) --> [what,is,my,middle,name].
%command(g(true,"Today you can find out about postgraduate study at the University of Bristol. This presentation is about the Centre for Doctoral Training in Interactive Artificial Intelligence")) --> today.
%command(g(true,"The presenter is the Centre Director, Professor Peter Flach")) --> todaysspeaker.

thanks --> [thank,you].
thanks --> [thanks].
thanks --> [great,thanks].

getanewfact --> getanewfact1.
getanewfact --> [tell,me],getanewfact1.

getanewfact1 --> [anything].
getanewfact1 --> [a,random,fact].
getanewfact1 --> [something,i,'don\'t',know].

kbdump --> [spill,the,beans].
kbdump --> [tell,me],allyouknow.

forget --> [forget].

forgetall --> [forget],allyouknow.

allyouknow --> all.
allyouknow --> all,[you,know].

all --> [all].
all --> [everything].

tellmeabout --> [tell,me,about].
tellmeabout --> [tell,me],all,[about].

rr(A):-random_member(A,["no worries","the pleasure is entirely mine","any time, peter","happy to be of help"]).

random_fact(X):-
	random_member(X,["walruses can weigh up to 1900 kilograms", "There are two species of walrus - Pacific and Atlantic", "Walruses eat molluscs", "Walruses live in herds","Walruses have two large tusks"]).


%%% various stuff for specfic events

% today --> [what,today,is,about].
% today --> [what,is,today,about].
% today --> [what,is,happening,today].
%
% todaysspeaker --> [who,gives,'today\'s',seminar].
% todaysspeaker --> [who,gives,it].
% todaysspeaker --> [who,is,the,speaker].
%
% peterflach --> [who,is],hepf.
% peterflach --> [tell,me,more,about],hepf.
%
% what --> [what,is],iai.
% what --> [tell,me,more,about],iai.
%
% hepf --> [he].
% hepf --> [peter,flach].
%
% iai --> [that].
% iai --> [interactive,'A.I.'].
% iai --> [interactive,artificial,intelligence].
%
% pf("According to Wikipedia, Pieter Adriaan Flach is a Dutch computer scientist and a Professor of Artificial Intelligence in the Department of Computer Science at the University of Bristol.").
%
% iai("The Centre for Doctoral Training in Interactive Artificial Intelligence will train the next generation of innovators in human-in-the-loop AI systems, enabling them to responsibly solve societally important problems. You can ask Peter for more information.").
%
