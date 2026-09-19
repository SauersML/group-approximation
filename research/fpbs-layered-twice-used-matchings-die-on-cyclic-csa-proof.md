---
rg: 2
id: fpbs-layered-twice-used-matchings-die-on-cyclic-csa-proof
kind: route
title: Letter mass count plus the two-occurrence relation forms (commensuration or square root) lock every layer into one malnormal maximal cyclic subgroup
target: fpbs-layered-twice-used-matchings-die-on-cyclic-csa
requires:
  - fpbs-bernoulli-morse-collapse-criterion
artifacts:
  - research/artifacts/fpbs-layered-twice-used-letter-towers-2026-09-18.md
---

Written proof, given in full in Sections 2–4 of the artifact.

1. **Mass count (Lemma 1).** By (M2) the removed edges are distinct. Each is an edge of an active letter, and each
   letter carries edge measure `1`. So `mu(M) <= |A|`. If two or more letters are unmatched, then
   `mu(M) <= |S| - 2`, and we are done.
2. **Relation forms (Lemma 2).** Let `c` be a matched `s_i`-cell. Rotate or invert its word to `s u s^{-1} v` or
   `s u s v`, where `u, v` are words in `H_{i+1} = <later active letters, U>`.
   - The two `s`-edges have bases `s^{-1}` and `(s u)^{-1}` in the first form, and `s^{-1}` and `(s u s)^{-1}` in
     the second. By freeness they coincide iff `u = 1` in the first form, and iff `g = s u = 1` in the second.
   - (M1) forces the two edges to be distinct. So either `s u s^{-1} ∈ H_{i+1}` with `u != 1`, or `g^2 = v^{-1} u`
     lies in `H_{i+1}` with `g != 1`.
3. **Base.** Suppose `|U| <= 1`. If `U` is empty, Lemma 2 at `s_n` needs a nontrivial element of the trivial group,
   or a nontrivial involution, and both are impossible. So `U = {t}` with `t != 1`. Put `E = C(t)`, which is cyclic.
4. **Step.** Assume `H_{i+1} <= E`.
   - In the commensuration form, `s E s^{-1} ∩ E != 1`. Malnormality gives `s ∈ E`.
   - In the root form, `1 != g^2 ∈ E`. By CSA, `g ∈ C(g^2) = E`, so `s = g u^{-1} ∈ E`.
5. **Conclusion.** `Gamma = H_1 <= E` is cyclic, which is a contradiction. Hence `mu(M) <= |S| - 2`.
   - On Bernoulli, `z(Phi_S) = |S| - 1 - beta_1^(2)` (Section 1 of the criterion) gives LTU deficit
     `>= 1 - beta_1^(2)`.
   - Theorem A(c) gives the certificate `|S| - mu(M) >= 2`.
6. **Standard inputs.**
   - Torsion-free hyperbolic groups are cyclic-CSA: centralizers of nontrivial elements are cyclic, and maximal
     cyclic subgroups are malnormal.
   - `beta_1^(2) = 0` for closed hyperbolic 3-manifold groups (Lott–Lück) and for property (T) groups.
   - Fixed price `1` for closed hyperbolic 3-manifold groups follows from Agol's virtual fibering and Gaboriau's
     infinite normal finitely generated subgroup criterion, with finite-index invariance of fixed price. It is used
     only as calibration and is not needed for the theorem.
