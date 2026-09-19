import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferAPI
import Mathlib

/-!
# Branch 4 — Transfer on the cell top class (Prompt 53)

This file proves the Branch-4 top-class theorem: the mod-2 cohomology transfer
`tr^! : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)` of the double cover sends the sphere top
cohomology class `u_S` to the RPⁿ top cohomology class `u_R`.

## The honest topological input

Following the module docstrings of `RPnTopClassTransferNonzero.lean` and
`Branch4TransferInventory.md`, the **one** genuinely missing algebraic-topology
input (absent from the pinned Mathlib) is that the homology transfer
`tr_* : Hₙ(RPⁿ; F₂) ⟶ Hₙ(Sⁿ; F₂)` carries the RPⁿ mod-2 top homology generator
`r_n` to the sphere mod-2 top homology generator `s_n`:
`tr_*(r_n) = s_n`. This is the geometric statement that the sum of the two
hemispherical lifts of the RPⁿ top cell is the mod-2 fundamental cycle of `Sⁿ`
(their common equatorial boundary cancels in characteristic two).

The project pins **no** named top-homology generators `s_n`, `r_n`, nor a named
sphere top cohomology class `u_S`. We therefore bundle exactly the data this
prompt requires — the two top homology generators, the sphere top cohomology
class, their dual-generator pairings, and the missing geometric transfer identity
`tr_*(r_n) = s_n` — into a single structure `B4TopData n`, alongside the honest
`RPnCellularCochainStructure n` cellular datum (which supplies one-dimensionality
of top RPⁿ cohomology) and the Branch-3 `MonodromyFunctional n` (which pins the
named RPⁿ top class `u_R = rpTopClass`). Everything after the bundled geometric
identity is the Kronecker adjunction plus rank-one linear algebra.

No `axiom`, `sorry`, `opaque`, or `p^*` (ordinary pullback) is used; the transfer
is the genuine wrong-way map `cohTransferZMod2` (`b4_cohTransferSphereToRP`).
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Bundled Branch-4 top-degree data for `Sⁿ`/`RPⁿ` over `F₂`.

It records the chosen mod-2 top homology generators `s_n = sphereTopHomGen` and
`r_n = rpTopHomGen`, the chosen sphere top cohomology class `u_S = sphereTopClass`
(the RPⁿ top class `u_R` is the named `b4_rpTopClass n monodromy`), together with
the characterizing dual-generator pairings and the genuinely-topological homology
transfer identity `tr_*(r_n) = s_n`. The cellular datum `cc` supplies
one-dimensionality of top RPⁿ cohomology. -/
structure B4TopData (n : ℕ) where
  /-- The Branch-3 monodromy functional pinning the named RPⁿ top class `u_R`. -/
  monodromy : MonodromyFunctional n
  /-- The honest cellular datum giving one-dimensional top RPⁿ cohomology. -/
  cc : RPnCellularCochainStructure n
  /-- The chosen sphere mod-2 top homology generator `s_n`. -/
  sphereTopHomGen : b4_sphereHomology n n
  /-- The chosen RPⁿ mod-2 top homology generator `r_n`. -/
  rpTopHomGen : b4_rpHomology n n
  /-- The chosen sphere top cohomology class `u_S`. -/
  sphereTopClass : b4_sphereCohomology n n
  /-- Dual-generator pairing on the sphere: `⟨u_S, s_n⟩ = 1`. -/
  sphere_pairing : b4_pairingSphere n n sphereTopClass sphereTopHomGen = 1
  /-- Dual-generator pairing on `RPⁿ`: `⟨u_R, r_n⟩ = 1`. -/
  rp_pairing : b4_pairingRP n n (b4_rpTopClass n monodromy) rpTopHomGen = 1
  /-- The homology transfer sends `r_n` to `s_n` (the geometric heart, bundled as
  the honest missing topological input). -/
  transfer_top :
    (b4_transferHomologyRPToSphere n n).hom rpTopHomGen = sphereTopHomGen

/-- **Step 1: homology top-generator transfer.** The mod-2 homology transfer
`tr_* : Hₙ(RPⁿ; F₂) ⟶ Hₙ(Sⁿ; F₂)` sends the RPⁿ top homology generator to the
sphere top homology generator. -/
theorem b4_transfer_top_homology_generator (n : ℕ) (d : B4TopData n) :
    (b4_transferHomologyRPToSphere n n).hom d.rpTopHomGen = d.sphereTopHomGen :=
  d.transfer_top

/-
**Step 2: nonzero version.** The cohomology transfer of the sphere top class
is nonzero.
-/
theorem b4_cohTransfer_sphereTopClass_ne_zero (n : ℕ) (d : B4TopData n) :
    (b4_cohTransferSphereToRP n n).hom d.sphereTopClass ≠ 0 := by
  intro h;
  convert d.sphere_pairing;
  have := b4_cohTransfer_kronecker n ( d.sphereTopClass ) ( d.rpTopHomGen ) ; simp_all +decide [ b4_pairingSphere, b4_pairingRP ];
  rw [ ← d.transfer_top, this.symm ] ; simp +decide

/-
**Step 3: equality with the named top class.** The cohomology transfer sends
the sphere top class `u_S` to the RPⁿ top class `u_R = b4_rpTopClass`.
-/
theorem b4_cohTransfer_sphereTopClass_eq_rpTopClass (n : ℕ) (d : B4TopData n) :
    (b4_cohTransferSphereToRP n n).hom d.sphereTopClass
      = b4_rpTopClass n d.monodromy := by
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, (b4_cohTransferSphereToRP n n).hom d.sphereTopClass = c • b4_rpTopClass n d.monodromy := by
    have h_finrank : Module.finrank (ZMod 2) (b4_rpCohomology n n) = 1 := by
      exact b4_rpTopCohomology_finrank_one n d.cc;
    rw [ finrank_eq_one_iff' ] at h_finrank;
    obtain ⟨ v, hv, hv' ⟩ := h_finrank; obtain ⟨ c, hc ⟩ := hv' ( b4_rpTopClass n d.monodromy ) ; obtain ⟨ d, hd ⟩ := hv' ( ( b4_cohTransferSphereToRP n n ).hom d.sphereTopClass ) ; use d * c⁻¹; by_cases hc' : c = 0 <;> simp_all +decide ;
    · have := ‹B4TopData n›.rp_pairing; simp_all +decide [ b4_pairingRP ] ;
      rw [ eq_comm ] at hc ; aesop;
    · rw [ ← hc, ← hd ] ; simp +decide [ hc', smul_smul ] ;
  fin_cases c <;> simp_all +decide;
  exact absurd hc ( b4_cohTransfer_sphereTopClass_ne_zero n d )

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
