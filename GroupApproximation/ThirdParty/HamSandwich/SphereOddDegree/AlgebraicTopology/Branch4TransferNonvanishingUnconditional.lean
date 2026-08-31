import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNonzero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferSurjective
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferAssembly
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferAPI
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Branch34OddMapFixesTopClassAssembly
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoTopGeneratorData
import Mathlib

/-!
# Prompt 05 — Prove the Branch-4 top-class transfer nonvanishing (no `transfer_top` black box)

This file discharges the genuine geometric payload of Branch 4 — the top-degree
nonvanishing of the double-cover transfer — **without** assuming the homology
transfer identity `tr_*(r_n) = s_n` (the `transfer_top` field of `B4TopData n`).

## What was previously assumed, and how it is now proved

The earlier Branch-4 layer bundled the top-degree nonvanishing into the field

```text
transfer_top : (b4_transferHomologyRPToSphere n n).hom rpTopHomGen = sphereTopHomGen
```

of `B4TopData n`, and derived `RPToSphereTransferTopNonzero n` /
`TopHomologyTransferNonzeroWitness n` from it.  That made the geometric heart a
free hypothesis.

Here the nonvanishing is instead **derived** from the genuine mod-2 *Smith short
exact sequence* of the double cover

```text
0 ⟶ C_•(RPⁿ; F₂) ──tr──▶ C_•(Sⁿ; F₂) ──proj_*──▶ C_•(RPⁿ; F₂) ⟶ 0,
```

whose dualized long exact cohomology sequence, together with the dimension
vanishing `Hⁿ⁺¹(RPⁿ; F₂) = 0`, shows the cohomology transfer
`cohTransferZMod2 n n : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)` is **surjective** in the top
degree (`cohTransferZMod2_top_surjective`).  Since both top groups are
one-dimensional over `F₂` (`rpCohomology_rank_one`, and `hsphere` for the sphere),
a surjection between equal finite dimensions is injective, hence the transfer is
nonzero on every nonzero top class.  Over `F₂`, Kronecker (universal-coefficient)
nondegeneracy then turns this into the homology-side witness.

## Honest remaining inputs

The two remaining inputs are exactly the project's standard cohomology-computation
data, **not** the geometric transfer identity:

* `c : RPnCellularCochainStructure n` — the additive cellular datum (supplies
  `Hⁿ⁺¹(RPⁿ; F₂) = 0` and `dim Hⁿ(RPⁿ; F₂) = 1`);
* `hsphere : Module.finrank (ZMod 2) (sphereCohomology n n) = 1` — top sphere
  cohomology rank one.

No `axiom`, `sorry`, `opaque`, `admit`, `constant`, or `unsafe` is used, and no
`B4TopData.transfer_top` field is consumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Elementary rank-one linear algebra.** A surjective `F₂`-linear map from a
one-dimensional space to a nontrivial space is injective on nonzero vectors: if
`T` is surjective, `dim V = 1`, `W` is nontrivial, `x ≠ 0` and `T x = 0`, we get a
contradiction. -/
private theorem b4u_ne_zero_of_surjective_finrank_one
    {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (T : V →ₗ[ZMod 2] W) (hs : Function.Surjective T)
    (hV : Module.finrank (ZMod 2) V = 1)
    {x : V} (hx : x ≠ 0) : T x ≠ 0 := by
  intro hTx
  have hspan : ∀ y : V, ∃ a : ZMod 2, y = a • x := by
    intro y
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hV y
    exact ⟨a, ha.symm⟩
  have hTzero : ∀ y : V, T y = 0 := by
    intro y
    obtain ⟨a, rfl⟩ := hspan y
    simp [hTx]
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hs w
  exact hw (hTzero v)

/-- Top mod-2 homology of `Sⁿ` (`n ≥ 1`) is one-dimensional over `F₂`: it is
spanned by the single nonzero generator of `SphereModTwoTopGeneratorData`. -/
theorem sphere_top_homology_finrank_one (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (homologyZMod2 (TopCat.of (Sphere n)) n) = 1 := by
  classical
  have D := construct_SphereModTwoTopGeneratorData n hn
  exact finrank_eq_one D.g D.g_ne (fun w => (D.spans w).imp (fun a ha => ha.symm))

/-- **Top sphere cohomology rank one, unconditionally for `n ≥ 1`.**  Over `F₂`
the Kronecker (universal-coefficient) isomorphism `kroneckerEquiv` identifies
`Hⁿ(Sⁿ; F₂)` with the linear dual of `Hₙ(Sⁿ; F₂)`, whose dimension equals that of
`Hₙ(Sⁿ; F₂) = 1`.  This discharges the `hsphere` rank-one input from `hn` alone. -/
theorem sphere_top_cohomology_finrank_one (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (sphereCohomology n n) = 1 := by
  have e : sphereCohomology n n ≃ₗ[ZMod 2]
      (homologyZMod2 (TopCat.of (Sphere n)) n →ₗ[ZMod 2] ZMod 2) :=
    (kroneckerEquiv (TopCat.of (Sphere n)) n).toLinearEquiv
  rw [e.finrank_eq]
  exact (Subspace.dual_finrank_eq).trans (sphere_top_homology_finrank_one n hn)

/-- **Top-degree nonvanishing of the cohomology transfer, from the cellular datum.**
For every nonzero top sphere cohomology class `x`, the genuine cohomology transfer
`cohTransferZMod2 n n` of `x` is nonzero.  Proved from top-degree surjectivity of
the transfer (the dualized Smith sequence plus `Hⁿ⁺¹(RPⁿ; F₂) = 0`) and rank one
of both top groups — **without** the `transfer_top` identity. -/
theorem RPToSphereTransferTopNonzero_of_cellular (n : ℕ)
    (c : RPnCellularCochainStructure n)
    (hsphere : Module.finrank (ZMod 2) (sphereCohomology n n) = 1) :
    RPToSphereTransferTopNonzero n := by
  intro x hx
  have hsurj : Function.Surjective (cohTransferZMod2 n n).hom :=
    cohTransferZMod2_top_surjective n c
  have hrp : Module.finrank (ZMod 2) (rpCohomology n n) = 1 :=
    rpCohomology_rank_one c n (le_refl n)
  haveI : Nontrivial (rpCohomology n n) :=
    Module.nontrivial_of_finrank_eq_succ (by simpa using hrp)
  exact b4u_ne_zero_of_surjective_finrank_one
    (cohTransferZMod2 n n).hom hsurj hsphere hx

/-- **The homology-side Kronecker witness, from the cellular datum.**  For every
nonzero top sphere class `c`, some `RPⁿ` top homology class `z` pairs nontrivially
with `c` after the homology transfer.

This is exactly `TopHomologyTransferNonzeroWitness n`, now derived from the honest
cellular datum and sphere rank one via the Smith-sequence surjectivity — the
`transfer_top` black box of `B4TopData` is no longer used. -/
theorem topHomologyTransferNonzeroWitness_of_cellular (n : ℕ)
    (c : RPnCellularCochainStructure n)
    (hsphere : Module.finrank (ZMod 2) (sphereCohomology n n) = 1) :
    TopHomologyTransferNonzeroWitness n := by
  intro cc hc
  -- The cohomology transfer of `cc` is nonzero.
  have htr : (cohTransferZMod2 n n).hom cc ≠ 0 :=
    RPToSphereTransferTopNonzero_of_cellular n c hsphere cc hc
  -- Over `F₂`, nonzero transfer means the Kronecker functional of `tr cc` is nonzero.
  rw [cohTransferZMod2_ne_zero_iff_kronecker] at htr
  -- A nonzero functional takes a nonzero value on some homology class `z`.
  obtain ⟨z, hz⟩ :
      ∃ z : homologyZMod2 (TopCat.of (RP n)) n,
        (kroneckerMap (TopCat.of (RP n)) n).hom ((cohTransferZMod2 n n).hom cc) z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact htr (by ext z; simpa using hcon z)
  refine ⟨z, ?_⟩
  -- Transfer–Kronecker adjunction: `⟨cc, tr_* z⟩ = ⟨tr cc, z⟩ ≠ 0`.
  rw [← cohTransferZMod2_kronecker_adjunction]
  exact hz

/-- **Branch-4 top-class transfer, from the cellular datum and sphere rank one.**
The project-level double-cover top-class transfer predicate `RPnTopClassTransfer n`
now follows from the honest cellular datum `c` and the sphere rank-one input
`hsphere` alone: the transfer nonvanishing input is *proved* here, not assumed. -/
theorem RPnTopClassTransfer_of_cellular_sphereRankOne (n : ℕ)
    (c : RPnCellularCochainStructure n)
    (hsphere : Module.finrank (ZMod 2) (sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  rpnTopClassTransfer_of_cellular_witness n c
    (topHomologyTransferNonzeroWitness_of_cellular n c hsphere)

/-- **`OddMapFixesTopClass n` from the honest cellular datum and sphere rank one,
with the transfer nonvanishing proved (no `B4TopData` / `transfer_top`).**

This is the payoff of removing the black box: the previously-monolithic input
`OddMapFixesTopClass n` is now a theorem consequence of exactly the two honest
cohomology-computation data used everywhere else — the cellular datum
`c : RPnCellularCochainStructure n` and the top sphere rank-one input `hsphere` —
with the Branch-4 top-class transfer *derived* from the Smith short exact sequence
rather than assumed. -/
theorem oddMapFixesTopClass_of_cellular_sphereRankOne
    (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n)
    (hsphere : Module.finrank (ZMod 2) (sphereCohomology n n) = 1) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_cellular_and_transfer n hn c
    (RPnTopClassTransfer_of_cellular_sphereRankOne n c hsphere)

/-! ## Strengthened forms with the sphere rank-one input discharged from `hn`

Using `sphere_top_cohomology_finrank_one`, the `hsphere` hypothesis is no longer
needed: for `n ≥ 1` the only remaining honest input is the cellular datum
`c : RPnCellularCochainStructure n`. -/

/-- Top-degree cohomology-transfer nonvanishing from `hn` and the cellular datum
alone (sphere rank one discharged internally). -/
theorem RPToSphereTransferTopNonzero_of_cellular_pos (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    RPToSphereTransferTopNonzero n :=
  RPToSphereTransferTopNonzero_of_cellular n c (sphere_top_cohomology_finrank_one n hn)

/-- The homology-side Kronecker witness from `hn` and the cellular datum alone. -/
theorem topHomologyTransferNonzeroWitness_of_cellular_pos (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    TopHomologyTransferNonzeroWitness n :=
  topHomologyTransferNonzeroWitness_of_cellular n c (sphere_top_cohomology_finrank_one n hn)

/-- Branch-4 top-class transfer from `hn` and the cellular datum alone. -/
theorem RPnTopClassTransfer_of_cellular_pos (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    RPnTopClassTransfer n :=
  RPnTopClassTransfer_of_cellular_sphereRankOne n c (sphere_top_cohomology_finrank_one n hn)

/-- **`OddMapFixesTopClass n` from `hn` and the honest cellular datum alone.**
The transfer nonvanishing and the sphere rank-one input are both proved; the sole
remaining honest input is the cellular datum `c : RPnCellularCochainStructure n`. -/
theorem oddMapFixesTopClass_of_cellular_pos (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_cellular_and_transfer n hn c
    (RPnTopClassTransfer_of_cellular_pos n hn c)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

