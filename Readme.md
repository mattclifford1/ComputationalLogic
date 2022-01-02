# M. Clifford, A. Davies

# Interactive Examples
Our added functionality is displayed in an online google colab notebook. [![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/mattclifford1/ComputationalLogic/blob/prolexa-plus/Prolexa_Plus_Demo_Notebook.ipynb)

# Extensions of prolexa

We worked on extending Prolexa to handle negation and existential quantification.

# Negation

Adding negation - queries of the type `is peter not happy` or responses `peter is not happy` - requires additions to `prolexa.pl`, which handles utterances, `prolexa_engine.pl` which conducts actual proofs and explanations, and `prolexa_grammar.pl`, which allows the use of natural language.

Firstly we extend `prove_question/3`, `prove_question/2`, and `explain_question/3`, to attempt the negative of a given query. For example, should the query be `is peter happy`, and the initial attempt to prove `happy(peter):-true` fails, prolexa now attempts to prove `not(happy(peter)) :- true`. In the case this succeeds it reponds, using additions to the grammar, `peter is not happy`. Should neither succeed it responds TODO --  `I'm not able to answer this` --.

`prove_question/2` is now as follows, with `prove_question/3`, and `explain_question/3` altered in the same manner:

```
prove_question(Query,Answer):-
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase),
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
```

Extending the grammar to handle queries was more complex. It needs to be able to deal not only with rules of the form `A(X):-B(X)`, `A(X) :- true` but also

- `not(A(X)):-not(B(X))`
- `not(A(X)):-B(X)`
- `A(X):-not(B(X))`
- `not(A(X)) :- true`

this required the addition of new determiners, verb phrases and questions for example:

```
determiner_neg(s,X=>H,X=>B,[(H:-not(B))]) --> [every].
determiner_neg(p,X=>H,X=>B,[(H:-not(B))]) --> [all].

question1(not(Q)) --> [is], proper_noun(N,X), [not], property(N,X=>Q).

neg_verb_phrase(s,M) --> [is, not],property(s,M).
neg_verb_phrase(p,M) --> [are, not],property(p,M).

```

We also add to the `prolexa.pl` main file to check if an added rule directly conflicts with an existing rule. For example `happy(peter)` should replace `not(happy(peter))` and vice versa. This is fairly simple to implement, and prevents conflicting rules in proofs:

```
% A. Utterance is a sentence
	( phrase(sentence(Rule),UtteranceList),
	  ( known_rule(Rule,SessionId) -> % A1. It follows from known rules
			atomic_list_concat(['I already knew that',Utterance],' ',Answer)
		; Rule = [(not(A) :- true)|_],
		 known_rule([(A:-true)],SessionId) -> % A2. It contradicts an existing rule
			retractall(prolexa:stored_rule(_,[(A:-true)])),
			atomic_list_concat(['I\'ll now remember that ',Utterance],' ',Answer),
			assertz(prolexa:stored_rule(SessionId,Rule))

		; Rule = [(A :- true)|_], % write_debug("trying negation, negative head"),
		  known_rule([(not(A):-true)],SessionId) -> % A2. It contradicts an existing rule
			retractall(prolexa:stored_rule(_,[(not(A):-true)])),
			atomic_list_concat(['I\'ll now remember that ',Utterance],' ',Answer),
			assertz(prolexa:stored_rule(SessionId,Rule))

	  ; otherwise -> % A3. It doesn't follow, so add to stored rules'
			assertz(prolexa:stored_rule(SessionId,Rule)),
			atomic_list_concat(['I will remember that',Utterance],' ',Answer)
	  )
```

After these additions, we use a rulebase such as

```
stored_rule(1,[(teacher(X):-happy(X))]).
stored_rule(1,[(not(teacher(X)):-not(happy(X)))]).
stored_rule(1,[(student(X):-not(teacher(X)))]).

stored_rule(1,[(teacher(peter):-true )]).
stored_rule(1,[(not(happy(maestro)):-true   )]).
```

(The 2nd rule is necessary in combination with the first - they do not imply the same thing. The first says that if you are happy you are a teacher, but the second says that everyone not happy is not a teacher, which does not follow from the first, as there could be some teachers who are not happy with only this first rule.)

The above rulebase allows the following interactions, demonstrating each of our added negation features

```
?- prolexa_cli.

prolexa> "is maestro a teacher".

maestro is not a teacher

prolexa> "who is not a teacher".

maestro is not a teacher

prolexa> "explain why maestro is a student".

maestro is not happy ; if not teacher then not happy ; every stud
ent is not a teacher ; therefore maestro is a student

prolexa> "tell me everything you know".

if happy then teacher. if not teacher then not happy. every stu
dent is not a teacher. peter is a teacher. maestro is not happy

prolexa> "maestro is happy".

I'll now remember that  maestro is happy

prolexa> "tell me everything you know".

if happy then teacher. if not teacher then not happy. every stu
dent is not a teacher. peter is a teacher. maestro is happy

prolexa>
```
# Existential Quantification
To handle adding rules such as `some humans are teachers` we need to add this to the grammar. This is done using skolem constants:
```
determiner(p,sk=>H1,sk=>H2,[(H1:-true),(H2:-true)]) --> [some].
```
This translates the sentence `some humans are teachers` to the rule `[(human(sk):-true),(teacher(sk):-true)]`, showing that there does indeed exist someone (sk) that is a human and also a teacher.

To ask questions such as `are some humans teachers` we add to the grammer the form of an existential question:
```
question_e(Q) --> qword,question1_e(Q).
question1_e((Q1,Q2)) --> [are,some],noun(p,sk=>Q1),property(p,sk=>Q2).
```
Which for the question `are some humans teachers` will give us the query in the form `human(sk),teacher(sk)`.

This is picked up in `prolexa.pl` using:
```
phrase(question_e(Query),UtteranceList)
```
to know that we are trying to prove the existential case.
## Proving existential queries
For the prover, we take inspiration from chaper 7.3 from the simply logical book. A different prover is needed since we now are trying to prove two separate facts are true (with the same ground atoms -> sk or other).
```
prove_rb_e(true,_Rulebase):-!.
prove_rb_e((A,B),Rulebase):-!,
    prove_rb_e(A,Rulebase),
    prove_rb_e(B,Rulebase).
prove_rb_e(A,Rulebase):-
    find_clause_e((A:-B),Rulebase),
    prove_rb_e(B,Rulebase).
```
This also allows us to infer existential facts like `some teachers are mortal` when using the rule `every human is mortal`:

```
?- prolexa_cli.

prolexa> "some humans are happy".

I will remember that some humans are happy

prolexa> "are some mortals happy".

some mortals are happy

prolexa>
```
this uses the rulebase

```
stored_rule(1,[(mortal(X):-human(X))]).

stored_rule(1,[(mortal(peter):-true)]).
stored_rule(1,[(teacher(peter):-true)]).
```



# Testing
Tests for added functionality are found in the [tests directory](./tests). Tests are also validated by on CircleCI's continuous integration server, see badge at the top of this readme.

[![CircleCI](https://circleci.com/gh/mattclifford1/ComputationalLogic/tree/prolexa-plus.svg?style=svg)](https://circleci.com/gh/mattclifford1/ComputationalLogic/tree/prolexa-plus)
