---
rg: 2
id: torsion-free-kazhdan-alternating-mother-limit-gate-proof
kind: route
title: Derive the exact torsion and simplicity gates for alternating marked limits of a torsion-free Kazhdan mother
target: torsion-free-kazhdan-alternating-mother-limit-gate
requires: []
---

**Primary inputs.**  Kaluba--Nowak--Ozawa, *`Aut(F_5)` has property
`(T)`*, Math. Ann. 375 (2019), prove property `(T)` for `Aut(F_5)` and note
that Gilman's theorem makes `Out(F_n)` residually finite alternating for
`n>=3`.  Baumslag--Taylor's torsion theorem for `Aut(F_n)`, as summarized in
Vogtmann's *Automorphisms of free groups and Outer space*, supplies
torsion-free finite-index subgroups of both `Aut(F_n)` and `Out(F_n)`.
Bridson--Vogtmann, *Homomorphisms from automorphism groups of free groups*,
prove that `Aut(F_n)` is the normal closure of one involution.  Finally,
Alekseev--Thom, *On non-isomorphic universal sofic groups*,
arXiv:2406.06741v3, Theorem 3.1 and the paragraph following it, state the
Bartholdi--Kassabov alternating-quotient theorem and explicitly identify the
eventual-separation strengthening as out of reach.

## 1. The torsion-free Kazhdan mother

Property `(T)` passes to quotients, so `Out(F_5)` has property `(T)`.  Choose
a torsion-free finite-index subgroup and replace it by its finite-index normal
core; call the result `Gamma_0`.  It remains torsion-free and has property
`(T)`, hence is finitely generated.

Let `q:Out(F_5)->>Alt(n)` be one of Gilman's alternating quotients.  Since
`Gamma_0` is normal, `q(Gamma_0)` is normal in `Alt(n)`, and hence is either
trivial or all of `Alt(n)`.  In the trivial case `q` factors through the fixed
finite group `Out(F_5)/Gamma_0`; consequently this can occur only while
`|Alt(n)|<=|Out(F_5)/Gamma_0|`.  Thus the restrictions to `Gamma_0` are
surjective for all sufficiently large degrees occurring in Gilman's
unbounded family.

Fix a finite marking `S` of `Gamma_0` and choose such epimorphisms
`q_i:Gamma_0->>Alt(n_i)` with `n_i->infinity`.  Compactness of the space of
`|S|`-marked groups gives a convergent subsequence, with limit `(K,S_bar)`.
Writing `F_S` for the marked free group, its kernel is

```text
N = { w in F_S : q_i(w)=1 eventually }.
```

Every relation of `Gamma_0` belongs to `N`, so `K` is a quotient of
`Gamma_0`; therefore it has property `(T)`.  A marked limit of finite groups
is LEF and hence sofic.  It is infinite: finite marked groups are isolated in
marked-group space, whereas the orders `|Alt(n_i)|` tend to infinity.

## 2. Exact torsion gate

For a word `w notin N`, the represented element of `K` has finite order `m`
exactly when `w^m in N`, equivalently when `q_i(w)^m=1` eventually.  Hence
`K` is torsion-free exactly when, for every persistent nonidentity `w` and
every `m>=1`, the equality `q_i(w)^m=1` does not eventually hold.  Because
truth of every fixed word relation stabilizes along a convergent marked
sequence, this is equivalent to `ord(q_i(w))->infinity` for every persistent
nonidentity word.

Notice that torsion-freeness of `Gamma_0` does not imply this condition:
quotients of torsion-free groups can acquire torsion.

## 3. Exact simple-limit gate

Suppose first that `K` is simple and let `w notin N`.  Each of the finitely
many marked generators lies in the normal closure of `w`.  Choose, once and
for all, expressions of those generators as finite products of conjugates of
`w` and `w^(-1)`.  Let `B_w` bound the numbers of factors and let `R_w` bound
the marking lengths of all conjugators appearing in these expressions.
Convergence says that the same word identities hold in every sufficiently
large `Alt(n_i)`.  These are the required bounded certificates.

Conversely, suppose such bounds `B_w,R_w` exist eventually for each
persistent `w`.  There are only finitely many products of at most `B_w`
conjugates by words of length at most `R_w`.  After passing to an infinite
subsequence, one certificate for each marked generator is constant.  Since
the sequence is convergent, an identity which holds infinitely often holds
eventually and hence in `K`.  Thus every marked generator belongs to the
normal closure of `w`; that normal closure is `K`.  Every nonidentity element
normally generates `K`, so `K` is simple.

This explains why simplicity of every finite factor does not pass formally
to the marked limit.  Finite simplicity provides a certificate at every
level, but gives neither a level-independent number of conjugates nor a
level-independent marking-length bound for the conjugators.

## 4. Two sharp exclusions

An infinite simple LEF group is not finitely presented: every finitely
presented LEF group is residually finite, while an infinite simple group has
no nontrivial finite quotient.  Thus a successful marked limit here must be
infinitely presented.  Nothing in the quotient construction organizes its
infinitely many relators into finitely many automorphism orbits, so it does
not provide the finite automorphic presentation needed to make a mapping
torus finitely presented.

Also, one cannot run the construction with the full `Aut(F_5)` or its
quotient `Out(F_5)`.  Let `tau` be Bridson--Vogtmann's normally generating
involution.  In any quotient, if the image of `tau` is trivial then the whole
quotient is trivial; otherwise its image is a nontrivial involution.  Hence
every nontrivial quotient has torsion.  Passing first to a torsion-free
finite-index subgroup is essential, but it discards this convenient normal
generator and does not solve the bounded-certificate gate.

Primary URLs:

```text
https://doi.org/10.1007/s00208-019-01874-9
https://arxiv.org/abs/math/0209191
https://arxiv.org/abs/2406.06741
https://arxiv.org/abs/2308.14529
```
