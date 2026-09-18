import GroupApproximation.Manuscript.NonMF.Full.AtomRepresentatives.AtomCells
import GroupApproximation.Meta.AxiomGuard

/-!
# The tower of `lem:transient-matrices` over first-atom representatives

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1512–1519:

> Order its atoms
> and select the point in the first occupied atom as the class
> representative.  [...]  On each cell the classes have a fixed size $h$
> and continuously enumerated clopen levels.
> The characteristic arrows between these levels form a copy of $M_h(k)$.

ms-units' tower family and expansion (`Dynamics/TransientTowerFamily`,
`Dynamics/TransientTowerExpansion`) index the levels of a cell from a base cell of least-exponent
representatives.  Over first-atom representatives (`exists_transientCells_atoms`) a cell `cell a`
has class exponents `S a`, which may be negative.  Translating the cell by the least exponent
`μ a` of `S a` gives a base cell with exponents `S a - μ a`, and the levels of the translated cell
are exactly the translates `T^d(cell a)`, `d ∈ S a`, of the atom cell (`image_zpow_image_zpow`):
the tower is the tower over the first-atom representatives, re-indexed from its lowest level.

* `zpow_mem_baseCell_of_min`: translating a point by the least exponent of its class lands in the
  base cell of the shifted exponents;
* `transientCellsStatement_atoms`: `ClopenCrossedProduct.TransientCellsStatement`, with cells the
  translated atom cells;
* `transientIdealLocallyMatricialStatement_atoms`: local matriciality of the transient ideal over
  every finite field, over the first-atom representatives.
-/

namespace GroupApproximation.Full.NM19

open GroupApproximation.ChainCore
open Multiplicative (toAdd)

section Translate

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-- **The levels over a translated cell** (tex 1517–1518): level `d` over `T^μ(A)` is level `d + μ`
over `A`. -/
theorem image_zpow_image_zpow (d μ : ℤ) (A : Set X) :
    ⇑(T ^ d) '' (⇑(T ^ μ) '' A) = ⇑(T ^ (d + μ)) '' A := by
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (Dynamics.zpow_apply_zpow_apply T d μ y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(T ^ μ) y, ⟨y, hy, rfl⟩, Dynamics.zpow_apply_zpow_apply T d μ y⟩

/-- **The lowest level is a base cell** (tex 1512–1517): translating a point of `C` by the least
exponent of its class gives a least-exponent representative with the shifted exponents. -/
theorem zpow_mem_baseCell_of_min (hm : ExponentBound T C m) {y : X} {μ : ℤ}
    (hμ : μ ∈ reachableExponents T C E (m - 1) y)
    (hμle : ∀ c ∈ reachableExponents T C E (m - 1) y, μ ≤ c) :
    (T ^ μ) y ∈ baseCell T C E m ((reachableExponents T C E (m - 1) y).image (· - μ)) := by
  have hR := reachableExponents_zpow_eq hm hμ
  refine ⟨⟨zpow_mem_of_mem_reachableExponents hμ, fun d hd => ?_⟩, hR⟩
  rw [hR, Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  have hc' := hμle c hc
  omega

end Translate

/-- **The cells of `lem:transient-matrices`** (tex 1510–1519), over first-atom representatives: the
atom cells of `exists_transientCells_atoms`, translated to their lowest level. -/
theorem transientCellsStatement_atoms : ClopenCrossedProduct.TransientCellsStatement := by
  intro X _ _ _ T k _ F hF
  obtain ⟨C, E, m, N, M, atom, cell, S, rep, hC, hCY, hm, hatoms, hcell, hsub, hS, hdisj, hcov,
    hrep, -, hsupp, hconst⟩ := exists_transientCells_atoms X T k F hF
  have hSne : ∀ a, (S a).Nonempty := fun a => ⟨0, by
    rw [← hS a (rep a) (hrep a)]
    exact zero_mem_reachableExponents (hsub a (hrep a)).1⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : Fin M → ℤ, μ = fun a => (S a).min' (hSne a) := ⟨_, rfl⟩
  have hμmem : ∀ a, μ a ∈ S a := fun a => by
    rw [hμdef]
    exact Finset.min'_mem _ _
  have hμle : ∀ a, ∀ c ∈ S a, μ a ≤ c := fun a c hc => by
    rw [hμdef]
    exact Finset.min'_le _ c hc
  have hbase : ∀ a, ∀ y ∈ cell a, (T ^ μ a) y ∈ baseCell T C E m ((S a).image (· - μ a)) :=
    fun a y hy => by
      have h := zpow_mem_baseCell_of_min (E := E) hm (y := y) (μ := μ a)
        (by rw [hS a y hy]; exact hμmem a) (fun c hc => hμle a c (by rw [← hS a y hy]; exact hc))
      rw [hS a y hy] at h
      exact h
  refine ⟨C, E, m, M, fun a => ⇑(T ^ μ a) '' cell a, fun a => (S a).image (· - μ a),
    fun a => Dynamics.isClopen_zpow_image T (μ a) (hcell a), fun a => (T ^ μ a) (rep a),
    hC, hCY, hm, ?_, ?_, ?_, fun a => Set.mem_image_of_mem _ (hrep a), hsupp, ?_⟩
  · intro a z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hbase a y hy
  · intro a b hab
    rw [Set.disjoint_left]
    intro z hza hzb
    obtain ⟨y, hy, rfl⟩ := hza
    obtain ⟨y', hy', hyy'⟩ := hzb
    have h := eq_of_zpow_eq_of_mem_atomBaseSet hm hatoms (hsub a hy) (hsub b hy')
      (by rw [hS a y hy]; exact hμmem a) (by rw [hS b y' hy']; exact hμmem b) hyy'.symm
    exact Set.disjoint_left.1 (hdisj a b hab) hy (by rw [h.1]; exact hy')
  · intro x hx
    obtain ⟨e, he, hex⟩ := exists_zpow_mem_atomBaseSet hm hatoms hx.1
    obtain ⟨a, ha⟩ := hcov _ hex
    refine ⟨a, (T ^ e) x, ha, ?_⟩
    have hneg : -e ∈ S a := by
      rw [← hS a _ ha]
      exact neg_mem_reachableExponents (m - 1) he
    have hlow : ∀ c ∈ S a, -e ≤ c := fun c hc => by
      rw [← hS a _ ha, reachableExponents_zpow_eq hm he, Finset.mem_image] at hc
      obtain ⟨c0, hc0, rfl⟩ := hc
      have hc0' : 0 ≤ c0 := hx.2 c0 hc0
      omega
    have hμe : μ a = -e := le_antisymm (hμle a _ hneg) (hlow _ (hμmem a))
    show (T ^ μ a) ((T ^ e) x) = x
    rw [hμe, Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  · intro x hx g hg a d hd z hz z' hz'
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', rfl⟩ := hz'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    rw [Dynamics.zpow_apply_zpow_apply, Dynamics.zpow_apply_zpow_apply, sub_add_cancel]
    exact hconst x hx g hg a c hc y hy y' hy'

/-- **`lem:transient-matrices`, the locally matricial clause** (tex 1476, 1517–1519), over the
tower of first-atom representatives. -/
theorem transientIdealLocallyMatricialStatement_atoms : TransientIdealLocallyMatricialStatement :=
  ClopenCrossedProduct.transientIdealLocallyMatricial_of_cells transientCellsStatement_atoms

end GroupApproximation.Full.NM19

#audit_axioms GroupApproximation.Full.NM19.image_zpow_image_zpow
#audit_axioms GroupApproximation.Full.NM19.zpow_mem_baseCell_of_min
#audit_axioms GroupApproximation.Full.NM19.transientCellsStatement_atoms
#audit_axioms GroupApproximation.Full.NM19.transientIdealLocallyMatricialStatement_atoms
