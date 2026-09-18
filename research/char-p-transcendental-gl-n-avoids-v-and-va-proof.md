---
rg: 2
id: char-p-transcendental-gl-n-avoids-v-and-va-proof
kind: route
title: SL_3(F_p[t]) has property (T), and the survey's cube-complex argument then excludes V and VA
target: char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3
requires: []
---

**Inputs** (classical; cited without re-reading at the source).
- (T1) `SL_3(F_p[t])` is a lattice in `SL_3(F_p((1/t)))`, since `F_p[t]` is discrete
  in `F_p((1/t))` (Harder). `SL_3` over a local field has Kazhdan's property (T),
  and lattices inherit (T) (Kazhdan; see Bekka--de la Harpe--Valette,
  *Kazhdan's Property (T)*, Chapter 1). So `SL_3(F_p[t])` is an infinite group
  with (T), and so is each of its finite-index subgroups.
- (T2) A group with (T) fixes a point in every action on a CAT(0) cube complex
  (Niblo--Roller; see Cornulier, arXiv:1302.5982, which the survey cites for
  this step). Quotients of (T) groups have (T).
- (S) Survey arXiv:2306.16356v3, Remark 4.12, verbatim: "using the CAT(0) cube
  complex from [BHM2] on which VA acts, we see that if SL_n(Z) embeds in VA then
  it virtually embeds in a vertex stabilizer, which is virtually an extension of
  one subgroup of V by another subgroup of V. Then repeatedly using the CAT(0)
  cube complex from [FarleyTV] on which V acts with finite stabilizers, we
  conclude that no such embedding can exist."

**Proof.**
- `F_p[t] <= K`, so the upper-left block gives `Γ := SL_3(F_p[t]) <= SL_n(K) <= GL_n(K)`
  for `n >= 3`. It suffices to show that the infinite (T) group `Γ` embeds in
  neither `V` nor `VA`.
- **V.** An embedding `Γ -> V` gives an action of `Γ` on Farley's cube complex.
  By (T2) `Γ` fixes a vertex, so it lies in a finite vertex stabilizer (S), a
  contradiction.
- **VA.** By (T2) `Γ` fixes a vertex of the [BHM2] cube complex, so some
  finite-index `Γ' <= Γ` lies in an extension `1 -> A -> E -> B -> 1` with
  `A, B <= V` (S).
  - The image of `Γ'` in `B` has (T), so it is finite by the V case.
  - So `Γ'' = Γ' ∩ A` has finite index in `Γ'`, has (T), and lies in `V`.
    It is therefore finite, and then `Γ` is finite, a contradiction.
- Subgroups of `V` and `VA` inherit the conclusion. `∎`

This is the survey's own argument for `SL_n(Z)`, with the Kazhdan lattice
`SL_3(F_p[t])` in place of `SL_n(Z)`.
