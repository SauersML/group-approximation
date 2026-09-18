import GroupApproximation.Dynamics.TransientCells
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# A finite clopen partition separating the points of each class

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1510–1512:

> Choose a finite clopen partition of $C$ separating distinct points
> in each class: the finitely many nonidentity partial shifts have no
> fixed points, so compactness gives such a partition.

Over theoremc-retire's `Dynamics/PartialShiftClasses` (`reachableExponents T C E (m - 1) x` is the
class of `x`, as exponents) this module proves:

* `zpow_apply_ne_of_exponentBound`: the orbit bound on `C` excludes periodic points of `C`, so a
  nonidentity partial shift has no fixed points;
* `IsSeparatingAtoms`: finitely many pairwise disjoint clopen atoms with union `C` such that two
  distinct points of one class never share an atom;
* `exists_separating_atoms`: such atoms exist for clopen `C` in a compact totally separated space.
  The finitely many exponent differences of all classes are nonzero, each point of `C` is
  separated from its translates by clopen sets, and compactness of `C` gives a finite subcover;
  the atoms are the disjointified pieces of that cover.
-/

namespace GroupApproximation.Full.NM19

open GroupApproximation.ChainCore
open Topology

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-- **No fixed points** (tex 1511–1512): under the orbit bound on `C`, a nonzero power of `T`
fixes no point of `C`. -/
theorem zpow_apply_ne_of_exponentBound (hm : ExponentBound T C m) {y : X} (hy : y ∈ C) {e : ℤ}
    (he : e ≠ 0) : (T ^ e) y ≠ y := by
  intro hfix
  have hiter : ∀ n : ℕ, (T ^ ((n : ℤ) * e)) y = y := by
    intro n
    induction n with
    | zero => rw [show ((0 : ℕ) : ℤ) * e = 0 by simp, zpow_zero, Homeomorph.one_apply]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) * e = (n : ℤ) * e + e by push_cast; ring,
        ← Dynamics.zpow_apply_zpow_apply, hfix, ih]
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) * e := by
    intro a b hab
    have h' : (a : ℤ) * e = (b : ℤ) * e := hab
    exact Nat.cast_inj.mp (mul_right_cancel₀ he h')
  have hcard := hm y ((Finset.range (m + 1)).image fun n : ℕ => (n : ℤ) * e) fun n hn => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hn
    rw [hiter k]
    exact hy
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hcard
  omega

/-- **Separating atoms** (tex 1510–1511): finitely many pairwise disjoint clopen atoms with union
`C`, such that distinct points of one class lie in distinct atoms. -/
structure IsSeparatingAtoms (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m N : ℕ)
    (atom : Fin N → Set X) : Prop where
  isClopen : ∀ i, IsClopen (atom i)
  disjoint : ∀ i j, i ≠ j → Disjoint (atom i) (atom j)
  iUnion_eq : C = ⋃ i, atom i
  separates : ∀ (x : X), ∀ d ∈ reachableExponents T C E (m - 1) x,
    ∀ d' ∈ reachableExponents T C E (m - 1) x, ∀ i,
      (T ^ d) x ∈ atom i → (T ^ d') x ∈ atom i → d = d'

/-- The clopen neighbourhood of `y` separating it from its translates by the exponents `D₂`. -/
def sepNbhd (T : X ≃ₜ X) (V : X → ℤ → Set X) (D₂ : Finset ℤ) (y : X) : Set X :=
  ⋂ e ∈ D₂, (V y e ∩ (T ^ e) ⁻¹' (V y e)ᶜ)

theorem mem_sepNbhd {V : X → ℤ → Set X} {D₂ : Finset ℤ} {y z : X} :
    z ∈ sepNbhd T V D₂ y ↔ ∀ e ∈ D₂, z ∈ V y e ∧ (T ^ e) z ∉ V y e := by
  simp only [sepNbhd, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]

theorem isClopen_sepNbhd {V : X → ℤ → Set X} (hV : ∀ y e, IsClopen (V y e)) (D₂ : Finset ℤ)
    (y : X) : IsClopen (sepNbhd T V D₂ y) := by
  show IsClopen (⋂ e ∈ D₂, (V y e ∩ (T ^ e) ⁻¹' (V y e)ᶜ))
  exact isClopen_biInter_finset fun e _ =>
    (hV y e).inter ((hV y e).compl.preimage (T ^ e).continuous)

/-- **A separating partition exists** (tex 1510–1512): for clopen `C` with the orbit bound in a
compact totally separated space. -/
theorem exists_separating_atoms [CompactSpace X] [TotallySeparatedSpace X] (hC : IsClopen C)
    (hm : ExponentBound T C m) (E : Finset ℤ) :
    ∃ (N : ℕ) (atom : Fin N → Set X), IsSeparatingAtoms T C E m N atom := by
  classical
  obtain ⟨D, hD⟩ := GroupApproximation.ClopenCrossedProduct.exists_finset_classExponents
    (T := T) (E := E) (m := m) hC
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : Finset ℤ,
      D₂ = ((D ×ˢ D).image fun p : ℤ × ℤ => p.2 - p.1).filter fun e => e ≠ 0 := ⟨_, rfl⟩
  have hsep : ∀ (y : X) (e : ℤ), ∃ V : Set X, IsClopen V ∧
      (y ∈ C → e ≠ 0 → y ∈ V ∧ (T ^ e) y ∉ V) := by
    intro y e
    by_cases h : y ∈ C ∧ e ≠ 0
    · obtain ⟨V, hV, hyV, hyV'⟩ :=
        exists_isClopen_of_totally_separated (zpow_apply_ne_of_exponentBound hm h.1 h.2).symm
      exact ⟨V, hV, fun _ _ => ⟨hyV, hyV'⟩⟩
    · exact ⟨∅, isClopen_empty, fun hy he => (h ⟨hy, he⟩).elim⟩
  choose V hV hVsep using hsep
  have hUmem : ∀ y ∈ C, y ∈ sepNbhd T V D₂ y := fun y hy => by
    refine mem_sepNbhd.2 fun e he => hVsep y e hy ?_
    rw [hD₂, Finset.mem_filter] at he
    exact he.2
  have hUnhds : ∀ y ∈ C, sepNbhd T V D₂ y ∈ 𝓝 y := fun y hy =>
    (isClopen_sepNbhd hV D₂ y).isOpen.mem_nhds (hUmem y hy)
  obtain ⟨t, -, hCt⟩ := hC.isClosed.isCompact.elim_nhds_subcover (sepNbhd T V D₂) hUnhds
  obtain ⟨W, hW⟩ : ∃ W : Fin t.card → Set X,
      W = fun i => sepNbhd T V D₂ (t.equivFin.symm i : X) := ⟨_, rfl⟩
  have hWc : ∀ i, IsClopen (W i) := fun i => by
    rw [hW]
    exact isClopen_sepNbhd hV D₂ _
  have hCW : C ⊆ ⋃ i, W i := by
    intro z hz
    obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.1 (hCt hz)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
    rw [hW]
    show z ∈ sepNbhd T V D₂ (t.equivFin.symm (t.equivFin ⟨y, hyt⟩) : X)
    rw [Equiv.symm_apply_apply]
    exact hzy
  refine ⟨t.card, Dynamics.coverPiece W C, ⟨fun i => Dynamics.isClopen_coverPiece W C hC hWc i,
    fun i j hij => Dynamics.disjoint_coverPiece W C hij, ?_, ?_⟩⟩
  · refine Set.Subset.antisymm (fun z hz => ?_)
      (Set.iUnion_subset fun j => (Dynamics.coverPiece_subset W C j).trans Set.inter_subset_left)
    obtain ⟨j, hj⟩ := Dynamics.exists_mem_coverPiece W C hCW hz
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  · intro x d hd d' hd' i hdi hd'i
    by_contra hne
    have he : d' - d ∈ D₂ := by
      rw [hD₂, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨(d, d'), Finset.mem_product.2 ⟨hD x hd, hD x hd'⟩, rfl⟩,
        by omega⟩
    have h1 : (T ^ d) x ∈ W i := ((Dynamics.coverPiece_subset W C i) hdi).2
    have h2 : (T ^ d') x ∈ W i := ((Dynamics.coverPiece_subset W C i) hd'i).2
    rw [hW] at h1 h2
    have hout := (mem_sepNbhd.1 h1 (d' - d) he).2
    have hin := (mem_sepNbhd.1 h2 (d' - d) he).1
    rw [Dynamics.zpow_apply_zpow_apply, sub_add_cancel] at hout
    exact hout hin

end GroupApproximation.Full.NM19

#audit_axioms GroupApproximation.Full.NM19.zpow_apply_ne_of_exponentBound
#audit_axioms GroupApproximation.Full.NM19.mem_sepNbhd
#audit_axioms GroupApproximation.Full.NM19.isClopen_sepNbhd
#audit_axioms GroupApproximation.Full.NM19.exists_separating_atoms
