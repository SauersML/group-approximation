---
rg: 2
id: universal-all-group-class-tester-proof
kind: route
title: Embed every finite presentation and take its unrestricted colimit
target: universal-all-group-subgroup-colimit-class-tester
requires:
  - whitehead-universal-finitely-presented-container
---

Fix the two-generator finitely presented group `U` from
[[whitehead-universal-finitely-presented-container]]. Only its ordinary
group-theoretic universality is needed below: every finitely presented group
is recursively presented, hence embeds in `U`.

Let `C` have the two permanence properties in the claim and assume `U`
belongs to `C`. Every finitely presented group `P` is a subgroup of `U`,
so subgroup closure gives `P` in `C`.

Now let `G` be an arbitrary group, with no countability assumption. Give the
elements of `G` formal generator names. For every finite set `S` of those
names and every finite set `R` of words on `S` which evaluate to the identity
in `G`, form

~~~text
P_(S,R)=<S | R>.
~~~

Order these data by adjoining finitely many generator names and finitely many
relations true in `G`. The evident maps form a directed system of finitely
presented groups. Its colimit is `G`: all multiplication and equality
relations true in `G` occur at some finite stage, while every stage has the
tautological map to `G`. This is the standard finite-presentation colimit of
an object in the variety of groups. The structure maps can be noninjective,
which is why arbitrary directed-colimit closure is explicitly assumed.

Every stage belongs to `C`, hence so does its colimit `G`. Conversely, if
every group belongs to `C`, then the particular group `U` does. Neither the
construction of `U` nor the argument depends on `C`, proving simultaneity.
QED
