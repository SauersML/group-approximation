---
rg: 2
id: lef-recognition-has-a-pi2-upper-bound
kind: claim
title: Local embeddability into finite groups is Pi-zero-two for recursive presentations
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that classifies the operator-norm MF property through microstates and a real-closed-field checker; this classifies LEF through finite groups and needs no analysis.
  lef-implies-operator-mf: that is the implication LEF => MF; this is the arithmetical complexity of LEF itself.
---

ESTABLISHED.  Uniformly in a recursive presentation `P = <X | r_1, r_2,
...>` of a finitely generated group `H`,

```text
H is LEF   iff   forall (W, N) [ (exists w in W, w = 1 in H)
                                  or (exists finite G, phi : X -> G,
                                      phi(r_j) = 1 for j <= N,
                                      phi(w) != 1 for all w in W) ],   (LEF1)
```

where `W` ranges over finite lists of words.  The first disjunct is `Sigma^0_1`
(the word problem of a recursive presentation is r.e.), and the second is
`Sigma^0_1` (search over finite groups given by multiplication tables and
over assignments; the check is decidable).  Hence LEF is `Pi^0_2`.  The same
normal form applies verbatim to finitely generated subgroups of a finitely
presented group given by generating tuples, since their induced presentation
is recursive.

## Proof of (LEF1)

(=>)  Let `H` be LEF and let `(W,N)` be a challenge with every `w in W`
nontrivial in `H`.  Let `n` bound the lengths of the words in `W` and of
`r_1, ..., r_N`.  LEF gives a finite group `G` and a map from the ball of
radius `n` of `H` to `G` that is injective and multiplicative where defined.
Composing with the evaluation of words gives `phi : X -> G` under which every
word of length at most `n` that is trivial in `H` (in particular each `r_j`,
`j <= N`) goes to `1`, and every nontrivial word of length at most `n` (in
particular each `w in W`) goes to a nontrivial element.

(<=)  Fix `n`.  Let `W` be the finite list of all words of length at most
`2n` that are nontrivial in `H`, and choose `N` so large that every word of
length at most `2n` that is trivial in `H` is a consequence of `r_1, ...,
r_N` (finitely many words, each with a finite derivation).  The challenge
`(W,N)` is not void, so there are `G` and `phi` as in `(LEF1)`.  Then `phi`
kills every trivial word of length at most `2n`, so it descends to a
well-defined map on the ball of radius `n` of `H`; it is multiplicative on
that ball by construction; and it is injective there because `u != v` in `H`
with `|u|,|v| <= n` means `u^-1 v in W`.  This is local embeddability at
radius `n`.

The point of the void disjunct is the same as in the MF normal form of
[[mf-recognition-has-a-pi2-upper-bound]]: a challenge that lists a trivial
word is discarded by a `Sigma^0_1` event, so the certificate never has to
assert that a word is nontrivial.
