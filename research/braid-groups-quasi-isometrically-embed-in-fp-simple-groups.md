---
rg: 2
id: braid-groups-quasi-isometrically-embed-in-fp-simple-groups
kind: claim
title: Braid groups, and mapping class groups of surfaces with boundary, quasi-isometrically embed in finitely presented simple groups
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that embeds braid groups and these mapping class groups in finitely presented simple groups through Aut(F_n), with no control of distortion; this gives embeddings that are quasi-isometric.
  aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups: that shows subgroups of Aut(F_n) keep their Aut(F_n)-distortion in the BFFHZ host; this supplies, for braid groups and bordered mapping class groups, an embedding into some Aut(F_m) that is undistorted.
  virtually-compact-special-groups-undistorted-in-2v: that uses the host 2V and reaches B_3 among braid groups; this uses a twisted Brin--Thompson host and reaches every B_n.
  loop-braid-groups-are-distorted-in-aut-free-groups: that shows the symmetric-automorphism route distorts loop braid groups; this avoids that route for braid groups by stabilizing with handles.
---

**ESTABLISHED** through `braid-group-qi-embedding-via-handle-capping-proof`. This is a lane proof, not
independently reviewed. No priority is claimed. A bounded search found no distortion statement in
BFFHZ (arXiv:2503.21882v2, TeX read) or in the Fournier-Facio--Wu--Zaremsky abstract (arXiv:2603.24687).

**Statement.**
1. For every `n >= 1` there is an injective homomorphism `ι_n: B_n → Aut(F_{2n})` that is a
   quasi-isometric embedding. Hence `B_n` is undistorted in the finitely presented simple group
   `SV_Γ`, `Γ = Aut_V(V * F_{2n})`, of BFFHZ Theorem A.
2. Let `Σ = S_g^b` be a compact orientable surface with `b >= 1`, and `Mod(Σ)` its mapping classes
   fixing `∂Σ` pointwise. There is an injective quasi-isometric embedding
   `Mod(Σ) → Aut(F_{2g+2b})`. So `Mod(Σ)` is undistorted in a finitely presented simple group.
   The annulus is the exception: there `Mod(Σ) ≅ Z`, which is undistorted in `V`
   (`thompson-v-cyclic-subgroups-are-undistorted`).
3. Every finitely generated group that is undistorted in some `B_n` or some `Mod(S_g^b)` with `b >= 1`
   quasi-isometrically embeds in a finitely presented simple group. For example, the Artin group of type
   `B_n` is the finite-index subgroup of `B_{n+1}` of braids whose permutation fixes one strand (standard;
   the annular braid group of BFFHZ's proof of Corollary B).

**What this answers.** Zaremsky (arXiv:2201.00711v1, TeX l.495–497) asks whether braid groups and mapping
class groups embed "(quasi-isometrically?)" in finitely presented simple groups. Part 1 answers the
quasi-isometric question for braid groups. Part 2 answers it for mapping class groups of surfaces with
boundary.

**Still open.**
- The "(even of type F_∞?)" refinement: it is not known whether this `SV_Γ` is of type F_∞.
- Mapping class groups of punctured surfaces without boundary: Boone--Higman is known for them (BFFHZ),
  but no quasi-isometric embedding is.
- Closed surfaces, `Out(F_n)` and CAT(0) groups: there even the plain embedding is open.
- Whether Artin's embedding `B_n → Aut(F_n)` is undistorted. It is not needed here.

**Lesson for general BH.** In the permutational route, the geometry of the embedding is decided by one
step. `SV_Γ` quasi-retracts onto its acting group `Γ` (Belk–Zaremsky), and BFFHZ's `Γ` retracts onto
`Aut(F_m)`. So "quasi-isometrically into a finitely presented simple group" for a subgroup of
`Aut(F_m)` is exactly undistortion in some `Aut(F_m)`. The embedding can then be chosen freely.
- The economical route (Artin, or the symmetric automorphisms) sits in a stabilizer of a free factor
  system of coindex at least 2, which Handel–Mosher show is distorted. Loop braid groups are in fact
  distorted there (`loop-braid-groups-are-distorted-in-aut-free-groups`).
- Stabilizing (capping each hole with a handle) moves the group into a once-punctured mapping class
  group, which is a Lipschitz retract (Hamenstädt–Hensel).

The transferable tool: for Boone–Higman with control of geometry, route the group through a chain of
retracts and subsurface inclusions, not through the smallest ambient group.
