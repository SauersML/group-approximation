import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Stable `K₂ = 0` passes to finite products (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  In the
Ara–Brustenga–Cortiñas computation of `K_*(C_2(𝔽₂))` (Münster J. Math. 2 (2009), proof of
Thm 3.6 and Sec. 5) the finite stages of the degree-zero part of the Cohn algebra are products
`𝔽₂ × M_2(𝔽₂) × ⋯ × M_{2^k}(𝔽₂)`, and `K₂` of a product is the product of the `K₂`s.  This file
proves the stable-`K₂ = 0` half of that additivity for arbitrary rings `R`, `S`:

* `nonUnitalMap`: a non-unital ring map `f` induces `St_I(R) → St_I(S)`, `x_{ij}(a) ↦ x_{ij}(f a)`
  (the Steinberg relations only use `+` and `*`);
* `inlHom`, `inrHom`: the non-unital inclusions `a ↦ (a, 0)` and `b ↦ (0, b)`;
* `inl_commute_inr`: when every pair of indices misses a third index, the images of `St_I(R)` and
  `St_I(S)` in `St_I(R × S)` commute;
* `eq_inl_mul_inr`: then every `g ∈ St_I(R × S)` equals `inl_* (fst_* g) · inr_* (snd_* g)`;
* `stableK2Trivial_prod`: stable `K₂(R) = 0` and stable `K₂(S) = 0` give stable `K₂(R × S) = 0`.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup
open scoped commutatorElement

section NonUnital

variable {I : Type*} [Fintype I] [DecidableEq I] {R S : Type*} [Ring R] [Ring S]

/-- Apply a non-unital ring map to the coefficient of a Steinberg generator.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def nonUnitalGenerator (f : R →ₙ+* S) (g : SteinbergGenerator I R) : SteinbergGroup I S :=
  x g.row g.column g.row_ne_column (f g.coefficient)

/-- The Steinberg relators are killed by a non-unital coefficient map.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem nonUnitalGenerator_relation (f : R →ₙ+* S) (w : FreeGroup (SteinbergGenerator I R))
    (hw : w ∈ relations (I := I) (R := R)) :
    FreeGroup.lift (nonUnitalGenerator f) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, nonUnitalGenerator]
      change x i j hij (f a) * x i j hij (f b) * (x i j hij (f (a + b)))⁻¹ = 1
      rw [x_mul, map_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, nonUnitalGenerator]
      change ⁅x i j hij (f a), x k l hkl (f b)⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli (f a) (f b)).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        nonUnitalGenerator]
      change ⁅x i j hij (f a), x j k hjk (f b)⁆ * (x i k hik (f (a * b)))⁻¹ = 1
      rw [x_commutator i j k hij hjk hik, map_mul, mul_inv_cancel]

/-- The homomorphism `St_I(R) → St_I(S)` induced by a non-unital ring map.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def nonUnitalMap (f : R →ₙ+* S) : SteinbergGroup I R →* SteinbergGroup I S :=
  PresentedGroup.toGroup (f := nonUnitalGenerator f) (nonUnitalGenerator_relation f)

/-- `nonUnitalMap f` on generators.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem nonUnitalMap_x (f : R →ₙ+* S) (i j : I) (hij : i ≠ j) (a : R) :
    nonUnitalMap f (x i j hij a) = x i j hij (f a) := by
  exact PresentedGroup.toGroup.of _

end NonUnital

/-- In `Fin N` with `3 ≤ N`, every two indices miss a third one.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_ne_ne_fin {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) :
    ∃ m : Fin N, m ≠ i ∧ m ≠ j := by
  by_cases hi0 : i.val = 0
  · by_cases hj1 : j.val = 1
    · exact ⟨⟨2, by omega⟩, Fin.ne_of_val_ne (show (2 : ℕ) ≠ i.val by omega),
        Fin.ne_of_val_ne (show (2 : ℕ) ≠ j.val by omega)⟩
    · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (show (1 : ℕ) ≠ i.val by omega),
        Fin.ne_of_val_ne (show (1 : ℕ) ≠ j.val by omega)⟩
  · by_cases hj0 : j.val = 0
    · by_cases hi1 : i.val = 1
      · exact ⟨⟨2, by omega⟩, Fin.ne_of_val_ne (show (2 : ℕ) ≠ i.val by omega),
          Fin.ne_of_val_ne (show (2 : ℕ) ≠ j.val by omega)⟩
      · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (show (1 : ℕ) ≠ i.val by omega),
          Fin.ne_of_val_ne (show (1 : ℕ) ≠ j.val by omega)⟩
    · exact ⟨⟨0, by omega⟩, Fin.ne_of_val_ne (show (0 : ℕ) ≠ i.val by omega),
        Fin.ne_of_val_ne (show (0 : ℕ) ≠ j.val by omega)⟩

section Product

variable (R S : Type*) [Ring R] [Ring S]

/-- The non-unital inclusion `a ↦ (a, 0)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def inlHom : R →ₙ+* R × S where
  toFun a := (a, 0)
  map_mul' _ _ := Prod.ext rfl (mul_zero (0 : S)).symm
  map_zero' := rfl
  map_add' _ _ := Prod.ext rfl (add_zero (0 : S)).symm

/-- The non-unital inclusion `b ↦ (0, b)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def inrHom : S →ₙ+* R × S where
  toFun b := (0, b)
  map_mul' _ _ := Prod.ext (mul_zero (0 : R)).symm rfl
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero (0 : R)).symm rfl

variable {R S} {I : Type*} [Fintype I] [DecidableEq I]

/-- `x_{ij}(a, 0)` commutes with `x_{jl}(0, b)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem commute_inl_inr_adjacent (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a : R) (b : S) :
    Commute (x i j hij ((a, 0) : R × S)) (x j l hjl ((0, b) : R × S)) := by
  have hab : ((a, 0) : R × S) * ((0, b) : R × S) = 0 := Prod.ext (mul_zero a) (zero_mul b)
  have h : ⁅x i j hij ((a, 0) : R × S), x j l hjl ((0, b) : R × S)⁆ = 1 :=
    (x_commutator i j l hij hjl hil ((a, 0) : R × S) ((0, b) : R × S)).trans
      ((congrArg (x i l hil) hab).trans (x_zero i l hil))
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- `x_{ij}(a, 0)` commutes with `x_{ki}(0, b)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem commute_inl_inr_adjacent' (i j k : I) (hij : i ≠ j) (hki : k ≠ i) (hjk : j ≠ k)
    (a : R) (b : S) :
    Commute (x i j hij ((a, 0) : R × S)) (x k i hki ((0, b) : R × S)) := by
  have hba : ((0, b) : R × S) * ((a, 0) : R × S) = 0 := Prod.ext (zero_mul a) (mul_zero b)
  have hkj : k ≠ j := fun e => hjk e.symm
  have h : ⁅x k i hki ((0, b) : R × S), x i j hij ((a, 0) : R × S)⁆ = 1 :=
    (x_commutator k i j hki hij hkj ((0, b) : R × S) ((a, 0) : R × S)).trans
      ((congrArg (x k j hkj) hba).trans (x_zero k j hkj))
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

/-- `x_{ij}(a, 0)` commutes with `x_{ji}(0, b)`, using a third index `m`: write
`x_{ij}(a, 0) = [x_{im}(a, 0), x_{mj}(1, 0)]` and apply the two adjacent cases.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_inl_inr_opposite (i j : I) (hij : i ≠ j) (m : I) (hmi : m ≠ i) (hmj : m ≠ j)
    (a : R) (b : S) :
    Commute (x i j hij ((a, 0) : R × S)) (x j i hij.symm ((0, b) : R × S)) := by
  have hA : Commute (x j i hij.symm ((0, b) : R × S)) (x i m hmi.symm ((a, 0) : R × S)) :=
    (commute_inl_inr_adjacent' i m j hmi.symm hij.symm hmj a b).symm
  have hB : Commute (x j i hij.symm ((0, b) : R × S)) (x m j hmj ((1, 0) : R × S)) :=
    (commute_inl_inr_adjacent m j i hmj hij.symm hmi (1 : R) b).symm
  have hC : Commute (x j i hij.symm ((0, b) : R × S))
      ⁅x i m hmi.symm ((a, 0) : R × S), x m j hmj ((1, 0) : R × S)⁆ := by
    rw [commutatorElement_def]
    exact ((hA.mul_right hB).mul_right hA.inv_right).mul_right hB.inv_right
  have ha1 : ((a, 0) : R × S) * ((1, 0) : R × S) = ((a, 0) : R × S) :=
    Prod.ext (mul_one a) (mul_zero (0 : S))
  have h : x i j hij ((a, 0) : R × S) =
      ⁅x i m hmi.symm ((a, 0) : R × S), x m j hmj ((1, 0) : R × S)⁆ :=
    ((x_commutator i m j hmi.symm hmj hij ((a, 0) : R × S) ((1, 0) : R × S)).trans
      (congrArg (x i j hij) ha1)).symm
  rw [h]
  exact hC.symm

/-- Generators with coefficients in `R × 0` and `0 × S` commute, provided every pair of indices
misses a third index.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem x_inl_commute_x_inr (hI : ∀ i j : I, ∃ m : I, m ≠ i ∧ m ≠ j)
    (i j : I) (hij : i ≠ j) (a : R) (k l : I) (hkl : k ≠ l) (b : S) :
    Commute (x i j hij ((a, 0) : R × S)) (x k l hkl ((0, b) : R × S)) := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hil : i = l
    · subst hil
      obtain ⟨m, hmi, hmj⟩ := hI i j
      exact commute_inl_inr_opposite i j hij m hmi hmj a b
    · exact commute_inl_inr_adjacent i j l hij hkl hil a b
  · by_cases hil : i = l
    · subst hil
      exact commute_inl_inr_adjacent' i j k hij hkl hjk a b
    · exact x_commute_of_ne i j k l hij hkl hjk (fun e => hil e.symm) _ _

/-- The images of `St_I(R)` and `St_I(S)` in `St_I(R × S)` commute, provided every pair of indices
misses a third index.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem inl_commute_inr (hI : ∀ i j : I, ∃ m : I, m ≠ i ∧ m ≠ j)
    (g : SteinbergGroup I R) (h : SteinbergGroup I S) :
    Commute (nonUnitalMap (inlHom R S) g) (nonUnitalMap (inrHom R S) h) := by
  have hgen : ∀ (i j : I) (hij : i ≠ j) (a : R) (h' : SteinbergGroup I S),
      Commute (x i j hij ((a, 0) : R × S)) (nonUnitalMap (inrHom R S) h') := by
    intro i j hij a h'
    have hmem : h' ∈ (Subgroup.centralizer {x i j hij ((a, 0) : R × S)}).comap
        (nonUnitalMap (I := I) (inrHom R S)) := by
      refine PresentedGroup.generated_by (relations (I := I) (R := S)) _ ?_ h'
      rintro ⟨k, l, hkl, b⟩
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      change x i j hij ((a, 0) : R × S) * nonUnitalMap (inrHom R S) (x k l hkl b) =
        nonUnitalMap (inrHom R S) (x k l hkl b) * x i j hij ((a, 0) : R × S)
      rw [nonUnitalMap_x]
      exact x_inl_commute_x_inr hI i j hij a k l hkl b
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hmem) _ (Set.mem_singleton _)
  have hmem : g ∈ (Subgroup.centralizer {nonUnitalMap (inrHom R S) h}).comap
      (nonUnitalMap (I := I) (inlHom R S)) := by
    refine PresentedGroup.generated_by (relations (I := I) (R := R)) _ ?_ g
    rintro ⟨i, j, hij, a⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    change nonUnitalMap (inrHom R S) h * nonUnitalMap (inlHom R S) (x i j hij a) =
      nonUnitalMap (inlHom R S) (x i j hij a) * nonUnitalMap (inrHom R S) h
    rw [nonUnitalMap_x]
    exact (hgen i j hij a h).symm
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hmem) _
    (Set.mem_singleton _)).symm

/-- The elements `g ∈ St_I(R × S)` with `g = inl_* (fst_* g) · inr_* (snd_* g)`; a subgroup when
every pair of indices misses a third index.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def prodDecompSubgroup (hI : ∀ i j : I, ∃ m : I, m ≠ i ∧ m ≠ j) :
    Subgroup (SteinbergGroup I (R × S)) where
  carrier := {g | g = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g) *
    nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) g)}
  one_mem' := by
    change (1 : SteinbergGroup I (R × S)) =
      nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) 1) *
        nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) 1)
    simp only [map_one, mul_one]
  mul_mem' := by
    intro g h hg hh
    change g = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) g) at hg
    change h = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) h) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) h) at hh
    change g * h = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) (g * h)) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) (g * h))
    have key := (inl_commute_inr hI (ringMap (RingHom.fst R S) h)
      (ringMap (RingHom.snd R S) g)).mul_mul_mul_comm
      (nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g))
      (nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) h))
    simp only [map_mul]
    rw [key, ← hg, ← hh]
  inv_mem' := by
    intro g hg
    change g = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) g) at hg
    change g⁻¹ = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g⁻¹) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) g⁻¹)
    simp only [map_inv]
    rw [(inl_commute_inr hI (ringMap (RingHom.fst R S) g)
      (ringMap (RingHom.snd R S) g)).inv_inv.eq, ← mul_inv_rev, ← hg]

/-- Every `g ∈ St_I(R × S)` equals `inl_* (fst_* g) · inr_* (snd_* g)`, provided every pair of
indices misses a third index.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem eq_inl_mul_inr (hI : ∀ i j : I, ∃ m : I, m ≠ i ∧ m ≠ j)
    (g : SteinbergGroup I (R × S)) :
    g = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) g) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) g) := by
  have hg : g ∈ prodDecompSubgroup hI := by
    refine PresentedGroup.generated_by (relations (I := I) (R := R × S)) _ ?_ g
    rintro ⟨i, j, hij, p⟩
    change x i j hij p = nonUnitalMap (inlHom R S) (ringMap (RingHom.fst R S) (x i j hij p)) *
      nonUnitalMap (inrHom R S) (ringMap (RingHom.snd R S) (x i j hij p))
    rw [ringMap_x, ringMap_x, nonUnitalMap_x, nonUnitalMap_x, x_mul]
    exact congrArg (x i j hij) (Prod.ext (add_zero p.1).symm (zero_add p.2).symm)
  exact hg

end Product

/-- **Products.**  Stable `K₂(R) = 0` and stable `K₂(S) = 0` give stable `K₂(R × S) = 0`: after
padding to rank `≥ 3`, `k ∈ K₂(n, R × S)` splits as `inl_* (fst_* k) · inr_* (snd_* k)`, and both
factors die after further padding.  (Ara–Brustenga–Cortiñas 2009, additivity of `K`-theory for
the finite stages `B_k` in Sec. 5; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_prod {R S : Type*} [Ring R] [Ring S] (hR : LVH2GL3.StableK2Trivial R)
    (hS : LVH2GL3.StableK2Trivial S) : LVH2GL3.StableK2Trivial (R × S) := by
  intro n k hk
  have hk₁ : projection (ringMap (I := Fin n) (RingHom.fst R S) k) = 1 := by
    rw [projection_ringMap, hk, map_one]
  have hk₂ : projection (ringMap (I := Fin n) (RingHom.snd R S) k) = 1 := by
    rw [projection_ringMap, hk, map_one]
  obtain ⟨N₁, h₁, hN₁⟩ := hR n (ringMap (I := Fin n) (RingHom.fst R S) k) hk₁
  obtain ⟨N₂, h₂, hN₂⟩ := hS n (ringMap (I := Fin n) (RingHom.snd R S) k) hk₂
  have hnM : n ≤ N₁ + N₂ + 3 := by omega
  have h1M : N₁ ≤ N₁ + N₂ + 3 := by omega
  have h2M : N₂ ≤ N₁ + N₂ + 3 := by omega
  have h3M : 3 ≤ N₁ + N₂ + 3 := by omega
  refine ⟨N₁ + N₂ + 3, hnM, ?_⟩
  have hfst : ringMap (RingHom.fst R S) (indexMap (Fin.castLEEmb hnM) k) = 1 := by
    rw [← LVStableK2.indexMap_ringMap,
      ← LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ h1M (ringMap (RingHom.fst R S) k), hN₁, map_one]
  have hsnd : ringMap (RingHom.snd R S) (indexMap (Fin.castLEEmb hnM) k) = 1 := by
    rw [← LVStableK2.indexMap_ringMap,
      ← LVH2GL3.indexMap_castLEEmb_castLEEmb h₂ h2M (ringMap (RingHom.snd R S) k), hN₂, map_one]
  rw [eq_inl_mul_inr (fun i j => exists_ne_ne_fin h3M i j) (indexMap (Fin.castLEEmb hnM) k),
    hfst, hsnd]
  simp only [map_one, mul_one]

end GroupApproximation.Full.LVCohnK2
