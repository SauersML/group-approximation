---
rg: 2
id: fpbs-malnormal-measured-absorption-cap-proof
kind: route
title: Transport the contact relation to a coset cocycle whose fibres are bounded by the stabilizer, then count disjoint translates
target: fpbs-malnormal-measured-absorption-cap
requires:
  - fpbs-wq-normal-hull-is-almost-malnormal
artifacts:
  - research/artifacts/fpbs-measured-absorption-cap-2026-09-17.md
---

Complete proof, written out in
`research/artifacts/fpbs-measured-absorption-cap-2026-09-17.md` §§0--4.

**Imports.**
- `fpbs-wq-normal-hull-is-almost-malnormal`, items 2--3 (`W(Lambda)` is almost
  malnormal and is built by the chain `W_{beta+1} = <W_beta, g : g W_beta g^{-1} ∩ W_beta infinite>`).
- Only for the positive Lemma 0, which is not needed for items 1, 2 or 4:
  Gaboriau, lecture notes, Exercise 1.17 (i)=>(iii), as quoted in
  `fpbs-wq-normal-price-one-subgroup-forces-price-one-proof`: "if almost every
  class of a standard p.m.p. equivalence relation is infinite, then for every
  `eps > 0` there is a complete section of measure at most `eps`."

**Item 1 (Theorem A).**
1. For `(x, h x) ∈ S_phi` with `h ∈ Lambda`, freeness turns
   `phi(hx) = h' phi(x)` into `gamma(hx) h = h' gamma(x)`. So the coset map
   `c(x) = Lambda gamma(x)` satisfies `c(hx) = c(x) h^{-1}`.
2. `Q(Lambda)` is a union of double cosets, so `B = {gamma ∉ Q(Lambda)}` is
   `S_phi`-invariant.
3. On a class in `B`, equal `c`-values force `h_1^{-1} h_2 ∈ Lambda ∩ gamma(x)^{-1} Lambda gamma(x)`,
   which is finite. So each fibre `c^{-1}(C)` meets each class in boundedly
   many points.
4. A Borel set meeting every class of an infinite-class subrelation of `E_a` in
   finitely many points is null. Split it by rank in a Borel order into sets
   meeting classes at most once, then use the enumeration of `Gamma` to build
   infinitely many pairwise disjoint measure-preserving translates.
5. `B ∩ D_phi(S)` is a countable union of such fibres, so it is null.

**Item 2.** `M = W(Lambda)` is almost malnormal and infinite, so `Q(M) = M`.
Apply item 1 with `Lambda := M` at every successor step. Limits are unions.

**Item 3.** The hull chain itself, with `S_beta = E_{a|W_beta}` and `phi = a(g)`
for `g ∈ Q(W_beta)`. The contact relation contains the orbits of the infinite
group `W_beta ∩ g^{-1} W_beta g`, so `D_phi = X`.

**Item 4.** `C(a) <= d_n + relC + 1` in one direction. In the other, split a
finite-cost generating graphing by labels and keep the pieces with labels
outside `M_n`. Their total mass tends to 0 by dominated convergence.
