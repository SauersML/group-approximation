---
rg: 2
id: commensurated-cat0-witnesses-force-finite-rational-cd
kind: claim
title: "If Sigma cap F is cut out by a compact open subgroup of a group acting with compact open stabilizers on a locally finite CAT(0) complex of dimension d (any Bruhat-Tits building in any characteristic, products of trees, cube complexes, right-angled buildings), then F/N acts properly on the fixed set of N and has rational cd at most d; so U, V, T, Thompson's F and Z wr Z have no such witness, while bounded ranks genuinely fail from d = 2 (Z/2 wr Z, SL_3(F_q[t]))"
distinct_from:
  commensurated-witnesses-survive-browder-but-die-when-linear: That kills characteristic-0 p-adic cut-outs by bounding finite-subgroup ranks (p-adic analytic) and tree cut-outs by Bass-Serre theory; this replaces the rank invariant by rational cohomological dimension, which survives in characteristic p and in every finite-dimensional CAT(0) geometry, where the rank bound provably fails.
  type-f-weyl-groups-have-bounded-elementary-abelian-ranks: That bounds elementary abelian ranks in Weyl groups of torsion-free pairs by Browder's theorem; this is a geometric kill for non-normalized cut-out witnesses and needs no torsion-freeness, finiteness type or homology.
  separable-benign-witness-forces-rf-quotient: That kills profinitely closed Sigma; the cut-outs here (e.g. congruence-type Sigma in characteristic-p S-arithmetic hosts) need not be profinitely closed, and the conclusion is dimensional, not residual finiteness.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`commensurated-witnesses-survive-browder-but-die-when-linear`: `F` free,
`N ⊴ F`, `P = F/N`.

**Theorem (CAT(0) cut-out kill).** Let `X` be a locally finite, piecewise
Euclidean (or `M_κ`, `κ ≤ 0`) CAT(0) polyhedral complex of dimension `d` with
finitely many shapes. Let `G` be a topological group acting continuously on
`X` by cellular isometries with compact open cell stabilizers. Let `K ≤ G` be
compact open, and `ρ : F -> G` any homomorphism with `N = F ∩ ρ^{-1}(K)`.
Then:

1. `Z = Fix(ρ(N))` is a nonempty convex subcomplex of the barycentric
   subdivision of `X`, of dimension `≤ d`, hence contractible. `F` preserves
   it, `N` acts trivially, and `P` acts on `Z` cellularly, without
   inversions, with **finite cell stabilizers**.
2. Hence `cd_Q P ≤ d`: every torsion-free subgroup of `P` has `cd ≤ d`, every
   free abelian subgroup has rank `≤ d`, and every finite subgroup of `P`
   fixes a vertex of `Z`.
3. For `d = 1`, `Z` is a tree and `P` is finite or virtually free (Step 5 of
   the cited proof), recovering the tree kill.

No torsion-freeness, finiteness type or commensuration hypothesis on the
witness is used; commensuration is automatic for such cut-outs when `Σ` is
the preimage of `K` in the host.

**Covered witnesses.**
- **Vertex stabilizers.** `Σ = Stab_Λ(v)` for any action of the host `Λ` on
  such an `X` (take `G = Aut(X)` with the permutation topology, `K = G_v`).
  This includes every witness in which `Σ` is a local group of a developable
  complex of groups over a finite complex with finite-index local maps and a
  CAT(0) development, e.g. irreducible
  lattices in products of trees and their factor stabilizers.
- **Linear cut-outs over every non-archimedean local field.** `G` a closed
  subgroup of `∏_j GL_{d_j}(k_j)`, each `k_j` a non-archimedean local field of
  **any characteristic**, acting on the product of extended Bruhat–Tits
  buildings, and `K` compact open in `G`. This includes characteristic-`p`
  S-arithmetic congruence witnesses (e.g. `Σ` a vertex stabilizer in one
  building factor of a torsion-free cocompact lattice from a division algebra
  over `F_q(t)`), which the `p`-adic analytic kill does not reach.
- **Schlichting form.** If the relative Schlichting completion `F̂` (proof of
  the cited claim, Step 6, with compact open normal `M` and `F̂/M ≅ P`) acts
  continuously on such an `X` with compact open cell stabilizers, the theorem
  applies with `K = M`. Conversely any such action of `P` inflates to `F̂`.
  So this class of completions is exactly the class where `P` itself acts
  properly on a finite-dimensional locally finite CAT(0) complex.
- **Right-angled buildings and cube complexes.** Automorphism groups of
  locally finite (finite-thickness) right-angled buildings and of locally
  finite finite-dimensional CAT(0) cube complexes.

**Consequences.** Higman's `U` contains `Z^n` for every `n` (it contains every
finitely presented group), and so do Thompson's `F`, `T`, `V` and `Z ≀ Z`
(which contains `Z^∞`). None of them is `F/N` for a witness of any kind above,
in any dimension, over any local field, with or without torsion in `Λ`.
In particular the three candidate classes named after
`commensurated-witnesses-survive-browder-but-die-when-linear`
(characteristic-`p` completions, right-angled building completions, and
non-tree Bruhat–Tits geometries) are dead for `N_U`.

**Sharpness: the rank invariant dies from dimension 2 (calibration).**
- `Z/2 ≀ Z = F_2[t^{±1}] ⋊ ⟨t⟩` is discrete in
  `Aff(F_2((t))) × Aff(F_2((t^{-1})))` and so acts properly on `T_3 × T_3`
  (`d = 2`) while containing `(Z/2)^r` for all `r`.
- `SL_3(F_q[t])` is finitely generated, discrete in `SL_3(F_q((t^{-1})))`,
  acts properly on its Ã_2 building, and contains the infinite elementary
  abelian group of unipotents `F_q[t]`.
So in characteristic `p` or in dimension `≥ 2`, no bound on finite-subgroup
ranks follows from the geometry; the correct surviving invariant is `cd_Q`.
This is why the `p`-adic analytic rank kill cannot extend. This kill does not
decide `Z/2 ≀ Z` (its torsion-free subgroups are cyclic, and it does act
properly on `T_3 × T_3`) or Grigorchuk's group (a finitely generated torsion
group, whose fixed-point behaviour on finite-dimensional CAT(0) complexes is
not settled here).

**Surviving shape for `N_U`.** A commensurated witness for `N_U` must have a
Schlichting completion `F̂` that admits no continuous action with compact open
stabilizers on any finite-dimensional locally finite CAT(0) complex; more
intrinsically `P = U` has `cd_Q U = ∞`, so every geometric model must be
infinite-dimensional (e.g. Farley-type cube complexes for Thompson-like
groups, Neretin-type almost-automorphism groups) or non-CAT(0).

Proof: route `commensurated-cat0-witnesses-force-finite-rational-cd-proof`.
