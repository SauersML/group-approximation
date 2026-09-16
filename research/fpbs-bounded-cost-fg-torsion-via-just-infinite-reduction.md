---
rg: 2
id: fpbs-bounded-cost-fg-torsion-via-just-infinite-reduction
kind: route
title: Pass to a just-infinite quotient, dispose of infinite centralizers, and apply the faithful just-infinite case
target: fpbs-bounded-cost-fg-torsion-quotient-price-one
requires:
  - fpbs-bounded-cost-just-infinite-faithful-price-one
  - fpbs-infinite-centralizer-forces-price-one
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

Written derivation. It is Theorem D in Section 5 of the linked artifact, with
Lemma B from Section 3. The outer-kernel hypothesis of the target is never
used, so the derivation proves the target without it.

**Setup.** Let `N ◁ Gamma` be infinite, and suppose every free p.m.p. action
of `N` has cost at most `K`. Call this (H_K). Let `Q = Gamma/N` be infinite,
finitely generated and torsion, with `pi : Gamma -> Q`.

**Lemma B (normal criterion).** If `N ◁ Lambda` is infinite and `Lambda` acts
freely, then `C(R_Lambda) <= C(R_N)`. So (H_K) passes from `N` to `Lambda`.
- Take a graphing of `R_N` of cost `C(R_N) + eps`, and coset representatives
  `gamma_j` of `N` in `Lambda`.
- Take Borel sets `A_j` meeting every `N`-orbit with `mu(A_j) <= eps 2^-j`.
  They exist since `N`-orbits are infinite. See Lemma B.0 of the artifact, or
  Exercise 1.17 of Gaboriau's notes as used in
  `fpbs-wq-normal-price-one-subgroup-forces-price-one-proof`.
- Add `gamma_j` restricted to `A_j`. If `lambda = gamma_j v` with `v in N`,
  and `w in N` with `w x in A_j`, then `lambda x = u gamma_j (w x)` with
  `u = gamma_j v w^-1 gamma_j^-1 in N`. So the enlarged graphing generates
  `R_Lambda`, at extra cost at most `eps`.

**Proof.**
1. **A just-infinite quotient.**
   - Let `P` be maximal among normal subgroups of `Q` of infinite index. It
     exists by Zorn's lemma: a union of a chain of such subgroups has infinite
     index, since otherwise it would be finitely generated and so equal to a
     member of the chain.
   - Then `Q/P` is infinite, and every nontrivial normal subgroup has finite
     index. It is finitely generated and torsion.
2. **Enlarge `N`.** Put `N_1 = pi^-1(P)`. Then `N_1 ◁ Gamma` contains `N`, and
   `Gamma/N_1 ≅ Q/P`. By Lemma B, `N_1` satisfies (H_K).
3. **Infinite centralizer.** If `C_Gamma(N_1)` is infinite,
   `fpbs-infinite-centralizer-forces-price-one` gives `Gamma` fixed price one.
4. **Finite centralizer.**
   - Otherwise `C_Gamma(N_1)` is a finite normal subgroup of `Gamma`.
   - Its image in `Q/P` is a finite normal subgroup of an infinite
     just-infinite group. Such a subgroup would have finite index, so it is
     trivial.
   - Hence `C_Gamma(N_1) ⊆ N_1`.
5. **Apply the faithful case.** `(Gamma, N_1)` satisfies every hypothesis of
   `fpbs-bounded-cost-just-infinite-faithful-price-one`. So `Gamma` has fixed
   price one.

**Converse.** In the setting of the premise, `C_Gamma(N) ⊆ N` makes the outer
kernel trivial. So the premise is a special case of the target, and the two
are equivalent given `fpbs-infinite-centralizer-forces-price-one`.

This is dependency bookkeeping for a written deduction, not a formal
verification.
