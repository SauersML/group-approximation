---
rg: 2
id: sound-rule-transfinite-closure-proof
kind: route
title: Radical pullback plus transfinite induction
target: sound-rule-transfinite-closure
requires: [universal-mf-quotient, mf-radical-functoriality]
---

## Why sufficient

As in `mf-relation-closure-proof`, the two prerequisites identify

```text
Rad_MF(G')  =  intersection of ker(f) over f : G' -> M, M countable MF   (*)
```

for every countable `G'`: functoriality gives one inclusion, and the
universal quotient `G' -> G'/Rad_MF(G')` is itself such an `f` with kernel
the radical.

**Key lemma (radical pullback).**  If `N <= Rad_MF(G)` is normal and
`q : G -> G/N`, then `q^{-1}(Rad_MF(G/N)) <= Rad_MF(G)`.  Proof: let
`q(x) in Rad_MF(G/N)` and let `f : G -> M` be any homomorphism to a
countable MF group.  By functoriality `f` kills `Rad_MF(G) >= N`, so
`f = fbar o q`; by functoriality applied to `fbar` and `(*)` on `G/N`,
`fbar` kills `Rad_MF(G/N)`, so `f(x) = fbar(q(x)) = 1`.  Intersecting over
`f` and using `(*)` on `G` gives `x in Rad_MF(G)`.

**Induction.**  `N_0 = 1 <= Rad_MF(G)`.  Successor: if
`N_alpha <= Rad_MF(G)`, soundness gives
`Delta(G/N_alpha) <= Rad_MF(G/N_alpha)`, so
`N_(alpha+1) = q_alpha^{-1}(Delta(G/N_alpha))
<= q_alpha^{-1}(Rad_MF(G/N_alpha)) <= Rad_MF(G)` by the lemma.  The chain
is increasing because the preimage contains `ker(q_alpha) = N_alpha`.
Limit: a union of normal subgroups of `Rad_MF(G)` along a chain is one.
This is item 1, hence item 3.

**Stabilization.**  Each strict step adds at least one element of the
countable group `G`, so the chain is strictly increasing along at most
countably many ordinals and stabilizes below `omega_1` — item 2.

**Completeness.**  If `G/Cl_Delta(G)` is MF, the quotient map is a
homomorphism to a countable MF group, so functoriality gives
`Rad_MF(G) <= Cl_Delta(G)`; with item 3 this is equality.  Conversely if
`Cl_Delta(G) = Rad_MF(G)`, the quotient is MF by `universal-mf-quotient` —
item 4.  Item 5 is item 3 read at `Cl_Delta(G) = G`.
