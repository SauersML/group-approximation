---
rg: 2
id: free-crossed-leavitt-k-gate-is-a-farrell-jones-instance
kind: claim
title: For any finitely generated group acting on a compact zero-dimensional space with free finite subgroups, K(B ⊗ L) vanishes iff the Farrell-Jones assembly map with coefficients LC(X, L) is an equivalence, so gate G3r is exactly one instance of Farrell-Jones
distinct_from:
  farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts: that proves K(B ⊗ L) = 0 when Λ satisfies Farrell-Jones; this shows the converse direction for this coefficient ring, for every Λ: the gate is equivalent to that single assembly statement, because the source of the assembly map always vanishes.
  free-action-leavitt-tensor-hosts-have-trivial-k1-k2: that is the open gate (K); this identifies it, for every Λ, with a Farrell-Jones instance, and draws the consequence for which routes can close it.
---

**ESTABLISHED** (lane proof, bh-algebra, a corollary of the route of
`farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`; not reviewed).

**Setting.** `Λ` is finitely generated. It acts on a compact Hausdorff zero-dimensional space `X`, and
every finite subgroup acts freely. `A` is the `Λ`-ring `LC(X, L)`, with `L = L_(F_2)(1,2)`, and
`B = LC(X, F_2) ⋊ Λ`, so that `B ⊗ L ≅ A ⋊ Λ`.

**Claim.** The source of the Farrell--Jones assembly map
`H_*^Λ(E_fbc Λ; K_A) -> K_*(A ⋊ Λ) = K_*(B ⊗ L)` vanishes, for every such `Λ`. Hence
`K_*(B ⊗ L) = 0` iff this assembly map is an equivalence, that is, iff the Farrell--Jones conjecture
holds for `Λ` with coefficients `A` relative to `fbc`. Relative to `VCyc` the same holds, by
`fj-family-reduces-to-finite-by-cyclic-with-coefficients`.

**Proof.** Steps 3 and 4 of `fj-groups-acting-freely-have-k-trivial-leavitt-hosts-proof` show that
`K(A ⋊ V) ≃ 0` for every finite and every finite-by-`Z` subgroup `V`. They use freeness of finite
subgroups but not the Farrell--Jones hypothesis, which that route uses only in its Step 2. So the
`Or(Λ)`-spectrum `K_A` is contractible at every orbit `Λ/V`, `V ∈ fbc`. The equivariant homology of
`E_fbc Λ`, whose isotropy lies in `fbc`, then vanishes (its cellular filtration has contractible
layers). An assembly map with contractible source is an equivalence iff its target is contractible. ∎

**Consequences for the master route** (`research/artifacts/gq-bh-synthesis-master-route.md`, gate G3r).
1. Gate G3r for a pair `(Λ, X)` is *equivalent* to one Farrell--Jones instance for `Λ`. The coefficients
   are "acyclic on virtually cyclic subgroups". Any proof of G3r for a `Λ` outside the known
   Farrell--Jones classes proves a new case of that conjecture.
2. The ring side of S1 puts `G <= Λ_0 <= Λ` with `G` an arbitrary decidable group (or `H_Γ`, which contains
   an arbitrary decidable `Γ`). It therefore needs this Farrell--Jones instance for acting groups that
   contain every decidable group. Choosing `Λ_0` inside a Farrell--Jones class with all coefficients is
   not possible in general, since that class is subgroup-closed and would force Farrell--Jones for `G`.
3. The ring-side routes that *fix* the acting group avoid this. With `Λ` a known Farrell--Jones group
   (for example `Z^2`, `F_2 × F_2`, a surface group or a lattice) carrying a free minimal quantum-rigid
   SFT, G3r is already established. The difficulty moves to embedding `G` in the unit group rather than
   in `Λ`: `boone-higman-via-units-of-cantor-crossed-leavitt-tensors`,
   `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`. There the complexity must come
   from the subshift `X` (its language) and not from `Λ`.

**Lesson for general BH.** On the ring side, the `K`-gate is not a technicality to be discharged
uniformly: it is precisely Farrell--Jones for the acting group with acyclic coefficients. So a universal
construction should keep the acting group in a fixed Farrell--Jones class, and load all input complexity
into the subshift and the unit group. Putting the input inside the acting group trades BH for a new case
of Farrell--Jones for groups containing arbitrary decidable groups. That is an independent open problem
of the same size.
