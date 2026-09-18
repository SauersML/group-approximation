---
rg: 2
id: psl2-q-fp-simple-via-rational-iwahori-rn-host
kind: route
title: A finitely presented self-similar overgroup of the rational Iwahori group puts PSL_2(Q) in a finitely presented simple commutator subgroup
target: psl2-q-embeds-in-fp-simple-group
requires:
  - pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori
  - rational-iwahori-group-lies-in-fp-self-similar-group
  - rover-nekrashevych-finite-presentation-criteria
---

Let `Λ` be as in `rational-iwahori-group-lies-in-fp-self-similar-group`.

1. **`PGL_2(Q) <= V_p(Λ)`.** `Γ_p <= Λ` inside `Aut(T_p)`, and both are
   self-similar with the same tree action. So every homeomorphism that is
   piecewise `φ ∘ γ ∘ φ^{-1}` with `γ ∈ Γ_p` is also piecewise with pieces in
   `Λ`, and `V_p(Γ_p) <= V_p(Λ)`. By
   `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`, item 3,
   `PGL_2(Q) <= V_p(Λ)`.
2. **`V_p(Λ)` is finitely presented.** This is (FP1, Scott) of
   `rover-nekrashevych-finite-presentation-criteria`, since `Λ` is finitely
   presented and self-similar.
3. **A finitely presented simple subgroup.** `K = [V_p(Λ), V_p(Λ)]` is simple,
   by item (S). It has finite index because `V_p(Λ)^ab` is finite. So it is
   finitely presented, by item (FP3).
4. **`PSL_2(Q) <= K`.** `PSL_2(Q)` is simple and nonabelian, hence perfect. It
   is the subgroup of `PGL_2(Q)` given by `SL_2(Q)`. Its image in `V_p(Λ)`
   therefore consists of products of commutators, and lies in `K`.

Hence `PSL_2(Q)` embeds in the finitely presented simple group `K`. The same
argument shows that `PGL_2(Q) ∩ K` has finite index in `PGL_2(Q)`.
