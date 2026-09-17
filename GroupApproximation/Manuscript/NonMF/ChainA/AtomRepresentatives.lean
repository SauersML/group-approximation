import GroupApproximation.Manuscript.NonMF.ChainA.SeparatingPartition
import GroupApproximation.Meta.AxiomGuard

/-!
# First occupied atoms, the clopen representative set, and the refined cells (tex 1504–1510)

`non_mf_groups_exist.tex`, proof of `lem:transient-matrices`, tex 1504–1510:

"Order its atoms and select the point in the first occupied atom as the class representative.
The representative set is clopen, because presence of a related point in an earlier atom is a
finite clopen test. Refine it according to the occupied atoms, the shift exponents to each level,
and all original coefficient values."

The setting is the same as in `SeparatingPartition`. The class of `x ∈ C` is
`{T^d x : d ∈ R x}`, where `R = reachableExponents T C E (m - 1)`, and `atom : X → Fin N` is a
locally constant map. The atoms are ordered by the order on `Fin N`.

Proof route.

* **Representatives.** `firstAtomSet` is the set of points of `C` whose atom is `≤` the atom of
  every related point. The class exponent `d₀` minimising `atom (T^d x)` exists
  (`Finset.exists_min_image`). It gives a representative, because the class of `T^{d₀} x` is the
  translate `R x - d₀` (`reachableExponents_zpow_eq`). Two representatives of one class lie in the
  same atom, so they coincide: distinct class points lie in distinct atoms.
* **Clopen test.** The key `x ↦ (atom x, R x, d ↦ atom (T^d x) for d ∈ R x)` is locally
  constant, and `firstAtomSet` is saturated for it. Preimages under a locally constant map are
  clopen. The complement in `C` is the set of points of `C` with a related point in an earlier
  atom.
* **Refinement.** The key `x ↦ (R x, d ↦ (atom (T^d x), coeff (T^d x)) for d ∈ R x)` is
  locally constant with finite range on the compact space. Its fibres cut `firstAtomSet` into
  finitely many clopen cells. On each cell the shift exponents to the levels, the occupied atoms
  and the coefficient values are constant.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainA

open GroupApproximation.ChainCore Topology

section Representatives

variable {X : Type*} [TopologicalSpace X]

/-- The representative set: points of `C` lying in the first occupied atom of their class. -/
def firstAtomSet (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) {N : ℕ} (atom : X → Fin N) :
    Set X :=
  C ∩ {x | ∀ d ∈ reachableExponents T C E (m - 1) x, atom x ≤ atom ((T ^ d) x)}

/-- The class key of `x`: its class exponents, and the values of `f` along the class. -/
def classKey (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) {W : Type*} (f : X → W) (x : X) :
    Finset ℤ × (ℤ → Option W) :=
  (reachableExponents T C E (m - 1) x,
    fun d => if d ∈ reachableExponents T C E (m - 1) x then some (f ((T ^ d) x)) else none)

variable {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

theorem mem_firstAtomSet_iff {N : ℕ} {atom : X → Fin N} {x : X} :
    x ∈ firstAtomSet T C E m atom ↔
      x ∈ C ∧ ∀ d ∈ reachableExponents T C E (m - 1) x, atom x ≤ atom ((T ^ d) x) :=
  Iff.rfl

/-- The class key of a locally constant map is locally constant. -/
theorem isLocallyConstant_classKey (hC : IsClopen C) {W : Type*} {f : X → W}
    (hf : IsLocallyConstant f) : IsLocallyConstant (classKey T C E m f) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hR : ∀ᶠ y in 𝓝 x,
      reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x :=
    (IsLocallyConstant.iff_eventually_eq _).1
      (isLocallyConstant_reachableExponents (T := T) (E := E) hC (m - 1)) x
  have hd : ∀ d ∈ reachableExponents T C E (m - 1) x,
      ∀ᶠ y in 𝓝 x, f ((T ^ d) y) = f ((T ^ d) x) := fun d _ =>
    (IsLocallyConstant.iff_eventually_eq _).1 (hf.comp_continuous (T ^ d).continuous) x
  filter_upwards [hR, (Filter.eventually_all_finset _).2 hd] with y hy1 hy2
  refine Prod.ext hy1 (funext fun d => ?_)
  show (if d ∈ reachableExponents T C E (m - 1) y then some (f ((T ^ d) y)) else none) =
    (if d ∈ reachableExponents T C E (m - 1) x then some (f ((T ^ d) x)) else none)
  by_cases hdx : d ∈ reachableExponents T C E (m - 1) x
  · have hdy : d ∈ reachableExponents T C E (m - 1) y := by
      rw [hy1]
      exact hdx
    rw [if_pos hdy, if_pos hdx, hy2 d hdx]
  · have hdy : d ∉ reachableExponents T C E (m - 1) y := by
      rw [hy1]
      exact hdx
    rw [if_neg hdy, if_neg hdx]

/-- Equal class keys give equal class exponents and equal values along the class. -/
theorem classKey_eq {W : Type*} {f : X → W} {x y : X}
    (h : classKey T C E m f y = classKey T C E m f x) :
    reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x ∧
      ∀ d ∈ reachableExponents T C E (m - 1) x, f ((T ^ d) y) = f ((T ^ d) x) := by
  have h1 : reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x :=
    congrArg Prod.fst h
  refine ⟨h1, fun d hdx => ?_⟩
  have hdy : d ∈ reachableExponents T C E (m - 1) y := by
    rw [h1]
    exact hdx
  have h2 : (if d ∈ reachableExponents T C E (m - 1) y then some (f ((T ^ d) y)) else none) =
      (if d ∈ reachableExponents T C E (m - 1) x then some (f ((T ^ d) x)) else none) :=
    congrFun (congrArg Prod.snd h) d
  rw [if_pos hdy, if_pos hdx] at h2
  exact Option.some.inj h2

/-- A set saturated for a locally constant map is clopen. -/
theorem isClopen_of_isLocallyConstant_saturated {Z : Type*} {g : X → Z}
    (hg : IsLocallyConstant g) {S : Set X} (hS : ∀ x y, g y = g x → y ∈ S → x ∈ S) :
    IsClopen S := by
  have h : S = g ⁻¹' (g '' S) := by
    refine Set.ext fun x => ⟨fun hx => ⟨x, hx, rfl⟩, fun hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hx
    exact hS x y hyx hy
  rw [h]
  exact ⟨⟨hg (g '' S)ᶜ⟩, hg (g '' S)⟩

/-- **The representative set is clopen.** -/
theorem isClopen_firstAtomSet (hC : IsClopen C) {N : ℕ} {atom : X → Fin N}
    (hatom : IsLocallyConstant atom) : IsClopen (firstAtomSet T C E m atom) := by
  refine isClopen_of_isLocallyConstant_saturated
    (hatom.prodMk (isLocallyConstant_classKey (T := T) (E := E) (m := m) hC hatom))
    fun x y hyx hy => ?_
  have hatomyx : atom y = atom x := congrArg Prod.fst hyx
  have hkey : classKey T C E m atom y = classKey T C E m atom x := congrArg Prod.snd hyx
  obtain ⟨hR, hd⟩ := classKey_eq hkey
  obtain ⟨hyC, hymin⟩ := mem_firstAtomSet_iff.1 hy
  refine mem_firstAtomSet_iff.2 ⟨?_, fun d hdx => ?_⟩
  · have h0 : (0 : ℤ) ∈ reachableExponents T C E (m - 1) x := by
      rw [← hR]
      exact zero_mem_reachableExponents hyC
    exact mem_of_mem_reachableExponents h0
  · have hdy : d ∈ reachableExponents T C E (m - 1) y := by
      rw [hR]
      exact hdx
    rw [← hatomyx, ← hd d hdx]
    exact hymin d hdy

/-- The complement of the representative set in `C` consists of the points with a related point in
an earlier atom. -/
theorem mem_diff_firstAtomSet_iff {N : ℕ} {atom : X → Fin N} {x : X} :
    x ∈ C \ firstAtomSet T C E m atom ↔
      x ∈ C ∧ ∃ d ∈ reachableExponents T C E (m - 1) x, atom ((T ^ d) x) < atom x := by
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hnot (mem_firstAtomSet_iff.2 ⟨hx, hcon⟩)
  · rintro ⟨hx, d, hd, hlt⟩
    exact ⟨hx, fun h => not_le.2 hlt ((mem_firstAtomSet_iff.1 h).2 d hd)⟩

/-- **The first occupied atom selects a unique representative** in every class. -/
theorem existsUnique_mem_firstAtomSet (hm : ExponentBound T C m) {N : ℕ} {atom : X → Fin N}
    (hsep : ∀ x ∈ C, ∀ d ∈ reachableExponents T C E (m - 1) x, d ≠ 0 → atom ((T ^ d) x) ≠ atom x)
    {x : X} (hx : x ∈ C) :
    ∃! d, d ∈ reachableExponents T C E (m - 1) x ∧ (T ^ d) x ∈ firstAtomSet T C E m atom := by
  obtain ⟨d0, hd0, hmin⟩ := Finset.exists_min_image (reachableExponents T C E (m - 1) x)
    (fun d => atom ((T ^ d) x)) ⟨0, zero_mem_reachableExponents hx⟩
  have hfirst : ∀ a ∈ reachableExponents T C E (m - 1) x,
      ((T ^ a) x ∈ firstAtomSet T C E m atom ↔
        ∀ b ∈ reachableExponents T C E (m - 1) x, atom ((T ^ a) x) ≤ atom ((T ^ b) x)) := by
    intro a ha
    rw [mem_firstAtomSet_iff, reachableExponents_zpow_eq hm ha]
    constructor
    · rintro ⟨-, h⟩ b hb
      have h' := h (b - a) (Finset.mem_image_of_mem (· - a) hb)
      rwa [GroupApproximation.Dynamics.zpow_apply_zpow_apply, sub_add_cancel] at h'
    · intro h
      refine ⟨zpow_mem_of_mem_reachableExponents ha, fun e he => ?_⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
      show atom ((T ^ a) x) ≤ atom ((T ^ (b - a)) ((T ^ a) x))
      rw [GroupApproximation.Dynamics.zpow_apply_zpow_apply, sub_add_cancel]
      exact h b hb
  refine ⟨d0, ⟨hd0, (hfirst d0 hd0).2 hmin⟩, fun d hd => ?_⟩
  by_contra hne
  have h1 : atom ((T ^ d) x) ≤ atom ((T ^ d0) x) := (hfirst d hd.1).1 hd.2 d0 hd0
  have h2 : atom ((T ^ d0) x) ≤ atom ((T ^ d) x) := hmin d hd.1
  exact atom_ne_of_mem_class hm hsep hd.1 hd0 hne (le_antisymm h1 h2)

/-- Finitely many clopen fibres of a locally constant map on a compact space partition a clopen
set. -/
theorem exists_fin_fibers [CompactSpace X] {Z : Type*} {key : X → Z}
    (hkey : IsLocallyConstant key) {S : Set X} (hS : IsClopen S) :
    ∃ (K : ℕ) (cell : Fin K → Set X), (∀ j, IsClopen (cell j)) ∧
      Pairwise (fun i j => Disjoint (cell i) (cell j)) ∧ (⋃ j, cell j) = S ∧
      ∀ j, ∀ x ∈ cell j, ∀ y ∈ cell j, key y = key x := by
  haveI : Finite (Set.range key) := hkey.range_finite.to_subtype
  refine ⟨Nat.card (Set.range key),
    fun j => S ∩ {x | key x = ((Finite.equivFin (Set.range key)).symm j).1},
    fun j => hS.inter (hkey.isClopen_fiber _), fun i j hij => ?_, ?_, fun j x hx y hy => ?_⟩
  · refine Set.disjoint_left.2 fun x hxi hxj => hij ?_
    have hi : key x = ((Finite.equivFin (Set.range key)).symm i).1 := hxi.2
    have hj : key x = ((Finite.equivFin (Set.range key)).symm j).1 := hxj.2
    exact (Finite.equivFin (Set.range key)).symm.injective (Subtype.ext (hi.symm.trans hj))
  · refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact hj.1
    · refine Set.mem_iUnion.2
        ⟨Finite.equivFin (Set.range key) ⟨key x, Set.mem_range_self x⟩, hx, ?_⟩
      have h := Equiv.symm_apply_apply (Finite.equivFin (Set.range key))
        ⟨key x, Set.mem_range_self x⟩
      exact (congrArg Subtype.val h).symm
  · have hx' : key x = ((Finite.equivFin (Set.range key)).symm j).1 := hx.2
    have hy' : key y = ((Finite.equivFin (Set.range key)).symm j).1 := hy.2
    exact hy'.trans hx'.symm

/-- **Refinement** (tex 1508–1510): finitely many clopen cells partition the representative set.
On each cell the class exponents are constant, and so are the occupied atoms and the coefficient
values along the class. -/
theorem exists_refined_cells [CompactSpace X] (hC : IsClopen C) {N : ℕ} {atom : X → Fin N}
    (hatom : IsLocallyConstant atom) {Z : Type*} {coeff : X → Z}
    (hcoeff : IsLocallyConstant coeff) :
    ∃ (K : ℕ) (cell : Fin K → Set X), (∀ j, IsClopen (cell j)) ∧
      Pairwise (fun i j => Disjoint (cell i) (cell j)) ∧
      (⋃ j, cell j) = firstAtomSet T C E m atom ∧
      ∀ j, ∀ x ∈ cell j, ∀ y ∈ cell j,
        reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x ∧
        ∀ d ∈ reachableExponents T C E (m - 1) x,
          atom ((T ^ d) y) = atom ((T ^ d) x) ∧ coeff ((T ^ d) y) = coeff ((T ^ d) x) := by
  obtain ⟨K, cell, hcl, hdisj, hU, hconst⟩ :=
    exists_fin_fibers (isLocallyConstant_classKey (T := T) (E := E) (m := m) hC
      (hatom.prodMk hcoeff)) (isClopen_firstAtomSet (T := T) (E := E) (m := m) hC hatom)
  refine ⟨K, cell, hcl, hdisj, hU, fun j x hx y hy => ?_⟩
  obtain ⟨hR, hd⟩ := classKey_eq (hconst j x hx y hy)
  refine ⟨hR, fun d hdx => ?_⟩
  have h := hd d hdx
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Representatives

/-- **tex 1504–1506.** "Order its atoms and select the point in the first occupied atom as the
class representative."

In the printed setting there are an orbit bound `m` and a separating clopen partition by atoms
`atom : X → Fin N`, ordered by `Fin N`. Every class `{T^d x : d ∈ R x}` has exactly one point in
the first occupied atom, i.e. exactly one point of `firstAtomSet`. -/
theorem manuscriptSentence_firstOccupiedAtomRepresentative {X : Type} [MetricSpace X]
    [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (C : Set X) (hC : IsClopen C)
    (hCY : Disjoint C (GroupApproximation.Dynamics.chainRecurrentSet ⇑T)) (E : Finset ℤ) :
    ∃ m : ℕ, ExponentBound T C m ∧
      ∃ (N : ℕ) (atom : X → Fin N), IsLocallyConstant atom ∧
        (∀ x ∈ C, ∀ a ∈ reachableExponents T C E (m - 1) x,
          ∀ b ∈ reachableExponents T C E (m - 1) x, a ≠ b → atom ((T ^ a) x) ≠ atom ((T ^ b) x)) ∧
        ∀ x ∈ C, ∃! d, d ∈ reachableExponents T C E (m - 1) x ∧
          (T ^ d) x ∈ C ∧
          ∀ e ∈ reachableExponents T C E (m - 1) ((T ^ d) x),
            atom ((T ^ d) x) ≤ atom ((T ^ e) ((T ^ d) x)) := by
  obtain ⟨m, -, -, -, -, hm⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_wandering_clopen_cover_of_isCompact T
      hC.isClosed.isCompact hCY
  obtain ⟨N, atom, hatom, hsep⟩ := exists_separating_atoms (E := E) hC hm
  exact ⟨m, hm, N, atom, hatom, fun _ _ _ ha _ hb hab => atom_ne_of_mem_class hm hsep ha hb hab,
    fun _ hx => existsUnique_mem_firstAtomSet hm hsep hx⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_firstOccupiedAtomRepresentative

/-- **tex 1506–1508.** "The representative set is clopen, because presence of a related point in
an earlier atom is a finite clopen test."

This holds for every clopen `C` and every locally constant atom map. The representative set is
clopen, its complement in `C` is clopen, and that complement is exactly the set of points of `C`
with a related point in an earlier atom. -/
theorem manuscriptSentence_representativeSetClopen {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)
    (C : Set X) (hC : IsClopen C) (E : Finset ℤ) (m N : ℕ) (atom : X → Fin N)
    (hatom : IsLocallyConstant atom) :
    IsClopen (firstAtomSet T C E m atom) ∧ IsClopen (C \ firstAtomSet T C E m atom) ∧
      ∀ x, x ∈ C \ firstAtomSet T C E m atom ↔
        x ∈ C ∧ ∃ d ∈ reachableExponents T C E (m - 1) x, atom ((T ^ d) x) < atom x :=
  ⟨isClopen_firstAtomSet hC hatom, hC.diff (isClopen_firstAtomSet hC hatom),
    fun _ => mem_diff_firstAtomSet_iff⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_representativeSetClopen

/-- **tex 1508–1510.** "Refine it according to the occupied atoms, the shift exponents to each
level, and all original coefficient values."

For a compact space, a clopen `C`, a locally constant atom map, and any locally constant
coefficient data `coeff : X → Z`, finitely many pairwise disjoint clopen cells partition the
representative set. On each cell the shift exponents to the levels, the occupied atoms and the
coefficient values at the levels are constant. -/
theorem manuscriptSentence_refineCells {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (T : X ≃ₜ X) (C : Set X) (hC : IsClopen C) (E : Finset ℤ) (m N : ℕ) (atom : X → Fin N)
    (hatom : IsLocallyConstant atom) {Z : Type*} (coeff : X → Z)
    (hcoeff : IsLocallyConstant coeff) :
    ∃ (K : ℕ) (cell : Fin K → Set X), (∀ j, IsClopen (cell j)) ∧
      Pairwise (fun i j => Disjoint (cell i) (cell j)) ∧
      (⋃ j, cell j) = firstAtomSet T C E m atom ∧
      ∀ j, ∀ x ∈ cell j, ∀ y ∈ cell j,
        reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x ∧
        ∀ d ∈ reachableExponents T C E (m - 1) x,
          atom ((T ^ d) y) = atom ((T ^ d) x) ∧ coeff ((T ^ d) y) = coeff ((T ^ d) x) :=
  exists_refined_cells hC hatom hcoeff

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_refineCells

end GroupApproximation.Manuscript.NonMF.ChainA
