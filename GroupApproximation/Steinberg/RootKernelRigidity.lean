import GroupApproximation.Steinberg.Basic

/-!
# Root-kernel rigidity for Steinberg groups

This file proves a purely internal normal-generation statement.  Over a ring
with strong two-sided division, killing one nonzero Steinberg root element
kills every root element, provided a spare index exists outside any four
prescribed indices.  Thus every nontrivial quotient map is injective on each
root subgroup.

No simplicity theorem, centrality theorem, or classification of normal
subgroups is used.
-/

namespace GroupApproximation
namespace SteinbergGroup

open scoped commutatorElement

variable {I R Q : Type*} [Fintype I] [DecidableEq I] [Ring R] [Group Q]

/-- If one nonzero root element dies, every root element dies.  The proof uses
only the defining Steinberg commutator relation and strong two-sided division.
-/
theorem map_x_eq_one_of_map_x_eq_one
    (hdiv : ∀ a : R, a ≠ 0 → ∃ u v : R, u * a * v = 1)
    (hspare : ∀ i j l k : I, ∃ r : I, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k)
    (φ : SteinbergGroup I R →* Q)
    {i j : I} (hij : i ≠ j) {a : R} (ha0 : a ≠ 0)
    (ha : φ (x i j hij a) = 1) :
    ∀ (l k : I) (hlk : l ≠ k) (d : R), φ (x l k hlk d) = 1 := by
  intro l k hlk d
  obtain ⟨r, hri, hrj, hrl, hrk⟩ := hspare i j l k
  have hir : i ≠ r := Ne.symm hri
  have jir : j ≠ r := Ne.symm hrj
  have lnr : l ≠ r := Ne.symm hrl
  have rnk : r ≠ k := hrk
  obtain ⟨u, v, huv⟩ := hdiv a ha0
  -- The killed `(i,j)` root first kills `x_{i,r}(a v)`.
  have hir_killed : φ (x i r hir (a * v)) = 1 := by
    rw [← x_commutator i j r hij jir hir a v, map_commutatorElement, ha]
    simp
  -- Left multiplication by `u` makes the coefficient exactly one in `(j,r)`.
  have hjr_one : φ (x j r jir 1) = 1 := by
    have hcoef : u * (a * v) = 1 := by simpa [mul_assoc] using huv
    have hcomm := x_commutator j i r (Ne.symm hij) hir jir u (a * v)
    have hmap := congrArg φ hcomm
    rw [map_commutatorElement, hir_killed, hcoef] at hmap
    simpa using hmap.symm
  by_cases hlj : l = j
  · subst l
    have hcomm := x_commutator j r k jir rnk hlk 1 d
    have hmap := congrArg φ hcomm
    rw [map_commutatorElement, hjr_one] at hmap
    simpa using hmap.symm
  · have hlr_killed : φ (x l r lnr d) = 1 := by
      have hcomm := x_commutator l j r hlj jir lnr d 1
      have hmap := congrArg φ hcomm
      rw [map_commutatorElement, hjr_one] at hmap
      simpa using hmap.symm
    have hcomm := x_commutator l r k lnr rnk hlk d 1
    have hmap := congrArg φ hcomm
    rw [map_commutatorElement, hlr_killed] at hmap
    simpa using hmap.symm

/-- Killing one nonzero root element makes a Steinberg homomorphism trivial. -/
theorem hom_eq_one_of_map_x_eq_one
    (hdiv : ∀ a : R, a ≠ 0 → ∃ u v : R, u * a * v = 1)
    (hspare : ∀ i j l k : I, ∃ r : I, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k)
    (φ : SteinbergGroup I R →* Q)
    {i j : I} (hij : i ≠ j) {a : R} (ha0 : a ≠ 0)
    (ha : φ (x i j hij a) = 1) :
    φ = 1 := by
  apply PresentedGroup.ext
  rintro ⟨l, k, hlk, d⟩
  change φ (x l k hlk d) = 1
  exact map_x_eq_one_of_map_x_eq_one hdiv hspare φ hij ha0 ha l k hlk d

/-- Every nontrivial quotient map is injective on each Steinberg root
subgroup. -/
theorem map_x_injective_of_ne_one
    (hdiv : ∀ a : R, a ≠ 0 → ∃ u v : R, u * a * v = 1)
    (hspare : ∀ i j l k : I, ∃ r : I, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k)
    (φ : SteinbergGroup I R →* Q) (hφ : φ ≠ 1)
    (i j : I) (hij : i ≠ j) :
    Function.Injective (fun a : R ↦ φ (x i j hij a)) := by
  intro a b hab
  by_contra hab0
  have hsub0 : a - b ≠ 0 := sub_ne_zero.mpr hab0
  have hkilled : φ (x i j hij (a - b)) = 1 := by
    have hmul : x i j hij (a - b) * x i j hij b = x (R := R) i j hij a := by
      rw [x_mul, sub_add_cancel]
    have hmap := congrArg φ hmul
    have hab' : φ (x i j hij a) = φ (x i j hij b) := hab
    rw [map_mul, hab'] at hmap
    apply mul_right_cancel (b := φ (x i j hij b))
    simpa using hmap
  exact hφ (hom_eq_one_of_map_x_eq_one hdiv hspare φ hij hsub0 hkilled)

/-- Every nonzero root element normally generates the whole Steinberg group
under strong two-sided division and the spare-index hypothesis. -/
theorem normalClosure_x_eq_top
    (hdiv : ∀ a : R, a ≠ 0 → ∃ u v : R, u * a * v = 1)
    (hspare : ∀ i j l k : I, ∃ r : I, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k)
    {i j : I} (hij : i ≠ j) {a : R} (ha0 : a ≠ 0) :
    Subgroup.normalClosure ({x i j hij a} : Set (SteinbergGroup I R)) = ⊤ := by
  let N : Subgroup (SteinbergGroup I R) :=
    Subgroup.normalClosure ({x i j hij a} : Set (SteinbergGroup I R))
  let q : SteinbergGroup I R →* SteinbergGroup I R ⧸ N := QuotientGroup.mk' N
  have hxN : x i j hij a ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hkill : q (x i j hij a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hxN
  have hq : q = 1 := hom_eq_one_of_map_x_eq_one hdiv hspare q hij ha0 hkill
  change N = ⊤
  calc
    N = q.ker := (QuotientGroup.ker_mk' N).symm
    _ = (1 : SteinbergGroup I R →* SteinbergGroup I R ⧸ N).ker :=
      congrArg MonoidHom.ker hq
    _ = ⊤ := MonoidHom.ker_one

/-- Every proper normal quotient remains injective on every root subgroup. -/
theorem quotientMap_x_injective
    (hdiv : ∀ a : R, a ≠ 0 → ∃ u v : R, u * a * v = 1)
    (hspare : ∀ i j l k : I, ∃ r : I, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k)
    (N : Subgroup (SteinbergGroup I R)) [N.Normal] (hN : N ≠ ⊤)
    (i j : I) (hij : i ≠ j) :
    Function.Injective (fun a : R ↦
      (QuotientGroup.mk' N) (x i j hij a)) := by
  have hq : (QuotientGroup.mk' N : SteinbergGroup I R →*
      SteinbergGroup I R ⧸ N) ≠ 1 := by
    intro htrivial
    apply hN
    calc
      N = (QuotientGroup.mk' N : SteinbergGroup I R →*
          SteinbergGroup I R ⧸ N).ker := (QuotientGroup.ker_mk' N).symm
      _ = (1 : SteinbergGroup I R →* SteinbergGroup I R ⧸ N).ker :=
        congrArg MonoidHom.ker htrivial
      _ = ⊤ := MonoidHom.ker_one
  exact map_x_injective_of_ne_one hdiv hspare (QuotientGroup.mk' N) hq i j hij

/-- Five or more finite coordinates supply an index outside any prescribed
four coordinates. -/
theorem fin_exists_spare_four {n : ℕ} (hn : 5 ≤ n) (i j l k : Fin n) :
    ∃ r : Fin n, r ≠ i ∧ r ≠ j ∧ r ≠ l ∧ r ≠ k := by
  classical
  by_contra h
  have hcover : ∀ r : Fin n, r = i ∨ r = j ∨ r = l ∨ r = k := by
    intro r
    by_contra hr
    push Not at hr
    exact h ⟨r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j, l, k} := by
    intro r _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcover r
  have hc1 : ({i, j, l, k} : Finset (Fin n)).card ≤ ({j, l, k} : Finset (Fin n)).card + 1 :=
    Finset.card_insert_le i {j, l, k}
  have hc2 : ({j, l, k} : Finset (Fin n)).card ≤ ({l, k} : Finset (Fin n)).card + 1 :=
    Finset.card_insert_le j {l, k}
  have hc3 : ({l, k} : Finset (Fin n)).card ≤ ({k} : Finset (Fin n)).card + 1 :=
    Finset.card_insert_le l {k}
  have hcard : n ≤ 4 := by
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
    have hle := Finset.card_le_card hsub
    have hsingleton : ({k} : Finset (Fin n)).card = 1 := Finset.card_singleton k
    omega
  omega

end SteinbergGroup
end GroupApproximation
