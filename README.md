[![CircleCI](https://circleci.com/gh/mattclifford1/ComputationalLogic/tree/prolexa-plus.svg?style=svg)](https://circleci.com/gh/mattclifford1/ComputationalLogic/tree/prolexa-plus)

## TODO

- Find examples of clauses, `teacher(matt):-true` and temporarily treat as rules

- Still need to follow every rules

- Some birds fly (`flies(tweepy):-true`)

- Some birds do not fly (`not(flies(opus)):-true`)

- `flies(tweepy):-true`, using `bird(tweepy) :- true`, to `flies(X) :- bird(X)` OR `bird(X) :- flies(X)`

- just need to find the set of ground atoms `flies(X), bird(X),...` ie `predicate(X)`

- # Check "hard rules" first, then call existential quantifiers if it doesnt work, only apply to "does" or "do" questions, not ground fact questions

# Interactive Examples
Our added functionality is displayed in an online google colab notebook. [![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/mattclifford1/ComputationalLogic/blob/prolexa-plus/Prolexa_Plus_Demo_Notebook.ipynb)

## Negation:

> Every teacher is happy. 
> Donald is not happy. 
> Therefore, Donald is not a teacher.

## Disjunction: 

> Pixels are red, blue or green. 
> Pixie is a pixel. 
> Pixie is not blue. 
> Therefore, Pixie is red or green.

## Existential quantification: 

> Some humans are geniuses.
> Geniuses win prizes. 
> Therefore, some humans win prizes.

## Abduction: 

> Most people infected with COVID-19 experience loss of taste. 
> Peter experiences loss of taste. 
> Therefore, (it is likely that) Peter is infected with COVID-19. 

## Default rules: 

> Most birds fly except penguins. 
> Tweety is a bird. 
> Therefore, assuming Tweety is not a penguin, Tweety flies. 





# Testing
Tests for added functionality are found in the [tests directory](./tests). Tests are also validated by on CircleCI's continuous integration server, see badge at the top of this readme.
