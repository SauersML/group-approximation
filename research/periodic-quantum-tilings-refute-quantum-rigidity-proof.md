---
rg: 2
id: periodic-quantum-tilings-refute-quantum-rigidity-proof
kind: route
title: Characters of the finite-dimensional image read off periodic configurations
target: periodic-quantum-tilings-refute-quantum-rigidity
requires: [sft-wall-rigidity-iff-idempotent-commutator-ideal]
artifacts:
  - research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md
---

The artifact, Section 4 (Theorem 4), gives the proof. Outline:

1. **Characters give periodic points.** Let `𝔅` be the image of `C_D` in `End(V)`. It is finite-dimensional
   and invariant under conjugation by `u^g`.
   - A one-dimensional composition factor gives a character `χ`. Since `χ(P_z^a) ∈ {0,1}` with one `1` per
     site, (Q3) makes the letter map `T_χ` locally admissible, so `T_χ ∈ Ω`.
   - `Z^2` permutes the finitely many maximal ideals of `𝔅`. So `ker χ` has a finite-index stabilizer, and
     `T_χ` is periodic, which is a contradiction.
   - A commuting family on `V` would have one-dimensional composition factors, so the family does not
     commute.
2. **Periodic families.** Over a finite field `GL(V)` is finite, so `u^λ = 1` on a finite-index subgroup,
   and `P_z` is periodic. Conversely, a periodic family on `W` gives the module of `Λ`-periodic maps
   `Z^2 -> W`, with the sitewise action of the `e_a` and translation by `u`.
3. **Wall-rigid case.** Apply Corollary 3.4 of the artifact, which is the composition-factor corollary of
   `sft-wall-rigidity-iff-idempotent-commutator-ideal`, to the noncommuting family on `V`.
