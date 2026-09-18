---
rg: 2
id: loop-braid-groups-are-distorted-in-aut-free-groups
kind: claim
title: For n >= 3 the symmetric automorphism groups of F_n, and so the loop braid groups, are distorted in Aut(F_n) and in the BFFHZ simple host
distinct_from:
  free-factor-system-stabilizers-distortion-dichotomy: that is the Handel--Mosher theorem in Out(F_n); this transfers it to Aut(F_n) for the free factor system of the basis letters, and draws the consequence for loop braid groups in the BFFHZ host.
  braid-groups-quasi-isometrically-embed-in-fp-simple-groups: that gives braid groups a quasi-isometric route into a finitely presented simple group; this shows that the natural route for loop braid groups is distorted.
---

**ESTABLISHED** through `loop-braid-distortion-from-free-factor-systems-proof`. This is a lane proof: a short
corollary of Handel–Mosher, not independently reviewed. No priority is claimed.

**Statement.** Let `n >= 3` and `F_n = ⟨x_1, …, x_n⟩`. Consider the following subgroups of `Aut(F_n)`:
- the extended symmetric automorphism group `Σ^±_n = {φ : φ(x_i) = w_i x_{π(i)}^{±1} w_i^{-1}, π ∈ S_n}`;
- its finite-index subgroups `Σ_n` (all signs `+`) and `PΣ_n` (also `π = id`, the McCool group).

All three are distorted in `Aut(F_n)`. Consequently they are also distorted in the finitely presented
simple group `SV_Γ`, `Γ = Aut_V(V * F_n)`, into which BFFHZ embed them, by part 2 of
`aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`.

**Loop braid groups.** Under the standard identification (Dahm, Goldsmith; see Damiani, *A journey
through loop braid groups*, Section 4, which BFFHZ cite), the loop braid group `LB_n` is `Σ_n` inside
`Aut(F_n)`. So the BFFHZ embeddings of `LB_n`, and of any group containing it with finite index, are not
quasi-isometric for `n >= 3`. Whether loop braid groups quasi-isometrically embed in some finitely
presented simple group is left OPEN.

**Contrast.** `B_n ≤ Σ_n` through Artin's embedding. This node does not decide whether `B_n` is distorted in
`Aut(F_n)`, and `braid-groups-quasi-isometrically-embed-in-fp-simple-groups` gets around the question with
a different embedding. For `n = 2`, the coindex is 1 and Handel–Mosher give a Lipschitz retract in `Out(F_2)`.

**Lesson for general BH.** The BFFHZ host is geometrically faithful to `Aut(F_n)`: it neither creates nor
removes distortion. So the Handel–Mosher coindex dichotomy predicts exactly which of its natural inputs
embed quasi-isometrically:
- coindex-1 stabilizers and free splitting stabilizers do;
- stabilizers of coindex ≥ 2 free factor systems, such as symmetric automorphisms and loop braids, do not.

For geometric refinements of Boone–Higman, the right object is therefore the class of groups undistorted in
the acting group of some type (A) action, not the class of subgroups.
