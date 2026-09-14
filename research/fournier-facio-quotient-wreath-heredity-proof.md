---
rg: 2
id: fournier-facio-quotient-wreath-heredity-proof
kind: route
title: A kernel meeting the simple factor swallows the group, so kernels miss every commuting copy
target: fournier-facio-nontrivial-quotients-contain-simple-wreath
requires:
  - fournier-facio-group-contains-simple-wreath-shift
  - defect-normally-generates-torsion-free-quotient
---

Let `N=ker phi`.  The intersection `N cap pi(S)` is normal in the simple
group `pi(S)`, so it is trivial or all of `pi(S)`.  In the second case
`<<pi(S)>>^G<=N`, and the established strong form of
`defect-normally-generates-torsion-free-quotient` gives `<<pi(S)>>^G=G`, so
`phi` is trivial.

Otherwise `N cap J_1=1`, and conjugating by powers of `t` gives
`N cap J_k=1` for every `k`.  Now repeat the injectivity arguments (W4) and
(W5) of `fournier-facio-simple-wreath-shift-proof` inside `phi(G)`.

- The images `phi(J_k)` pairwise commute and are isomorphic to the centerless
  group `S`.  The kernel of the sum map
  `(+)_k J_k -> phi(G)` is normal and meets each summand trivially, so it is
  trivial.
- If `phi(nu(a tau^m))=1` with `m!=0`, then conjugation by `phi(t)^m` would
  identify `phi(J_0)` with `phi(J_m)` elementwise, as in (W5), while the sum
  map is injective.  This is impossible.

So `phi o nu` is injective.

For the direct-product clause: `phi(C)` with `C=mu((+)_(k<=0) J_k)`
centralizes `phi(Gamma)`, and `phi(C)` is a direct sum of centerless groups.
So `phi(Gamma) cap phi(C)` is central in `phi(C)`, hence trivial.

The consequences follow because subgroups of hyperlinear groups are
hyperlinear.
