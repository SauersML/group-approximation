import GroupApproximation.CharClass.WuSymmetric

/-!
# The diagonal Wu relation for mod-2 Chern classes

For a complex vector bundle `E` with mod-2 Chern classes `γ_j(E)` the *diagonal*
Wu relation reads

```text
(Wu-diag)      Sq^{2i}( γ_{i+1} )  =  ∑_{j = 0}^{i} γ_{i-j} · γ_{i+1+j} .
```

It is the only Wu relation the parity argument of `ParityEven.lean` uses, and at
`j = i+1` all the binomial coefficients of the general Wu formula collapse to one,
so no arithmetic mod two is needed anywhere.

## What this file assumes

The relation is proved here over the abstract structure `SqData σ A` bundling
**exactly** the facts the derivation uses:

* `A` is a commutative ring with `2 = 0` (a graded `ZMod 2`-algebra, with the
  grading discarded: it plays no role in this argument);
* an additive operation `Sq : ℕ → A →+ A` with `Sq^0 = id` and the Cartan
  formula `Sq^n (u v) = ∑_{p ≤ n} Sq^p u · Sq^{n-p} v`;
* a finite family `y : σ → A` indexed by `s : Finset σ` — the Chern roots of the
  splitting principle, of degree two — with
  `Sq^1 y = 0`, `Sq^2 y = y²` and `Sq^n y = 0` for `n ≥ 3`.

The last item is what "`y` has degree two and `Sq(y) = y + y²`" says once the
grading is forgotten; the instability axiom `Sq^n = 0` above the degree is used
only in that specialized form, so it is not a separate field.  `γ_j := e_j(y)`
is then the `j`-th elementary symmetric function of the roots, which is what the
splitting principle delivers for a mod-2 Chern class.

## The proof

Applying `Sq^{2i}` to a squarefree monomial `∏_{l ∈ C} y_l` and using the Cartan
formula picks, from each factor, either `y_l` (degree unchanged) or `y_l²`
(degree raised by two); with `|C| = i + 1` and `2i` degrees to raise, exactly `i`
of the factors get squared.  This is `sq_prod`, an induction on `C` in which the
odd squares are carried along and shown to vanish.  Summing over the
`(i+1)`-element subsets `C ⊆ s` gives the right-hand side of
`esymm_halfAntidiagonal_eq` in its pair form, and that lemma converts it into
`∑_{j ≤ i} e_{i-j} e_{i+1+j}`.

`Sq^n 1 = 0` for `n > 0` is *derived* from the Cartan formula and `Sq^0 = id`
rather than assumed: `Sq^n 1 = Sq^n (1·1) = 2 · Sq^n 1 = 0` once every strictly
smaller positive square of `1` vanishes.

## Main results

* `GroupApproximation.CharClass.SqData.wu_diagonal` — (Wu-diag) for `γ_j = e_j(y)`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Finset

/-! ### `Sq` of a squarefree monomial, as a sum over subsets -/

section Monomial

variable {σ A : Type*} [CommRing A] [DecidableEq σ]

/-- `wuMonomialOn C y c` is what `Sq^{2c}` produces from the squarefree monomial
`∏_{l ∈ C} y_l`: choose `c` of the factors to square. -/
def wuMonomialOn (C : Finset σ) (y : σ → A) (c : ℕ) : A :=
  ∑ B ∈ C.powersetCard c, (∏ l ∈ B, y l ^ 2) * ∏ l ∈ C \ B, y l

theorem wuMonomialOn_def (C : Finset σ) (y : σ → A) (c : ℕ) :
    wuMonomialOn C y c = ∑ B ∈ C.powersetCard c, (∏ l ∈ B, y l ^ 2) * ∏ l ∈ C \ B, y l := rfl

theorem wuMonomialOn_zero (C : Finset σ) (y : σ → A) :
    wuMonomialOn C y 0 = ∏ l ∈ C, y l := by
  rw [wuMonomialOn_def, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty,
    Finset.sdiff_empty, one_mul]

theorem wuMonomialOn_empty_of_pos (y : σ → A) {c : ℕ} (hc : 0 < c) :
    wuMonomialOn (∅ : Finset σ) y c = 0 := by
  have h : (∅ : Finset σ).powersetCard c = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hc)
  rw [wuMonomialOn_def, h, Finset.sum_empty]

/-- Adjoining a variable to the monomial: the new factor is either left alone or
squared. -/
theorem wuMonomialOn_insert {w : σ} {C : Finset σ} (hw : w ∉ C) (y : σ → A) (c : ℕ) :
    wuMonomialOn (insert w C) y (c + 1)
      = y w * wuMonomialOn C y (c + 1) + y w ^ 2 * wuMonomialOn C y c := by
  have hps : (insert w C).powersetCard (c + 1)
      = C.powersetCard (c + 1) ∪ (C.powersetCard c).image (insert w) :=
    Finset.powersetCard_succ_insert hw c
  have hdisj : Disjoint (C.powersetCard (c + 1)) ((C.powersetCard c).image (insert w)) := by
    rw [Finset.disjoint_right]
    intro B hB hB'
    rw [Finset.mem_image] at hB
    obtain ⟨E, _, rfl⟩ := hB
    exact hw ((Finset.mem_powersetCard.mp hB').1 (Finset.mem_insert_self w E))
  have hinj : Set.InjOn (fun E : Finset σ => insert w E) ↑(C.powersetCard c) := by
    intro E hE F hF hEF
    have hE' : E ∈ C.powersetCard c := hE
    have hF' : F ∈ C.powersetCard c := hF
    have hwE : w ∉ E := fun h => hw ((Finset.mem_powersetCard.mp hE').1 h)
    have hwF : w ∉ F := fun h => hw ((Finset.mem_powersetCard.mp hF').1 h)
    have hEF' : insert w E = insert w F := hEF
    rw [← Finset.erase_insert hwE, ← Finset.erase_insert hwF, hEF']
  have hblock1 : ∑ B ∈ C.powersetCard (c + 1),
        (∏ l ∈ B, y l ^ 2) * ∏ l ∈ insert w C \ B, y l
      = y w * wuMonomialOn C y (c + 1) := by
    rw [wuMonomialOn_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hBC : B ⊆ C := (Finset.mem_powersetCard.mp hB).1
    have hwB : w ∉ B := fun h => hw (hBC h)
    have hwCB : w ∉ C \ B := by
      simp only [Finset.mem_sdiff, not_and]
      exact fun h => absurd h hw
    rw [Finset.insert_sdiff_of_notMem C hwB, Finset.prod_insert hwCB]
    ring
  have hblock2 : ∑ B ∈ (C.powersetCard c).image (insert w),
        (∏ l ∈ B, y l ^ 2) * ∏ l ∈ insert w C \ B, y l
      = y w ^ 2 * wuMonomialOn C y c := by
    rw [Finset.sum_image hinj, wuMonomialOn_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    have hEC : E ⊆ C := (Finset.mem_powersetCard.mp hE).1
    have hwE : w ∉ E := fun h => hw (hEC h)
    have hsd : insert w C \ insert w E = C \ E := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hk1 | hk1, hk2, hk3⟩
        · exact absurd hk1 hk2
        · exact ⟨hk1, hk3⟩
      · rintro ⟨hk1, hk2⟩
        exact ⟨Or.inr hk1, fun h => hw (h ▸ hk1), hk2⟩
    rw [hsd, Finset.prod_insert hwE]
    ring
  calc wuMonomialOn (insert w C) y (c + 1)
      = (∑ B ∈ C.powersetCard (c + 1), (∏ l ∈ B, y l ^ 2) * ∏ l ∈ insert w C \ B, y l)
        + ∑ B ∈ (C.powersetCard c).image (insert w),
            (∏ l ∈ B, y l ^ 2) * ∏ l ∈ insert w C \ B, y l := by
        rw [wuMonomialOn_def, hps]
        exact Finset.sum_union hdisj
    _ = y w * wuMonomialOn C y (c + 1) + y w ^ 2 * wuMonomialOn C y c := by
        rw [hblock1, hblock2]

end Monomial

/-! ### The abstract Steenrod data -/

/-- Exactly the facts the diagonal Wu relation is derived from: a commutative ring
of characteristic two, an additive operation `Sq` with `Sq^0 = id` and the Cartan
formula, and a finite family `y` of degree-two classes with `Sq(y) = y + y²`. -/
structure SqData (σ : Type*) (A : Type*) [CommRing A] where
  /-- The coefficients are `ZMod 2`. -/
  two_eq_zero : (2 : A) = 0
  /-- The Steenrod squares, additive in the class. -/
  Sq : ℕ → A →+ A
  /-- `Sq^0` is the identity. -/
  sq_zero_apply : ∀ a : A, Sq 0 a = a
  /-- The Cartan formula. -/
  cartan : ∀ (n : ℕ) (u v : A),
    Sq n (u * v) = ∑ p ∈ Finset.range (n + 1), Sq p u * Sq (n - p) v
  /-- The index set of the Chern roots. -/
  s : Finset σ
  /-- The Chern roots, of cohomological degree two. -/
  y : σ → A
  /-- `Sq^1` kills a degree-two class that is the reduction of an integral one. -/
  sq_y_one : ∀ k : σ, Sq 1 (y k) = 0
  /-- The top square of a degree-two class is its square. -/
  sq_y_two : ∀ k : σ, Sq 2 (y k) = y k ^ 2
  /-- Instability for a degree-two class. -/
  sq_y_high : ∀ (k : σ) (n : ℕ), 3 ≤ n → Sq n (y k) = 0

namespace SqData

variable {σ A : Type*} [CommRing A] (D : SqData σ A)

/-- `Sq` shifted down by two: the coefficient of `y_k²` in the Cartan expansion of
`Sq^n (y_k · u)`. -/
def sqShift : ℕ → A → A
  | 0, _ => 0
  | 1, _ => 0
  | (n + 2), u => D.Sq n u

@[simp] theorem sqShift_zero (u : A) : D.sqShift 0 u = 0 := rfl

@[simp] theorem sqShift_one (u : A) : D.sqShift 1 u = 0 := rfl

@[simp] theorem sqShift_add_two (n : ℕ) (u : A) : D.sqShift (n + 2) u = D.Sq n u := rfl

/-- The Cartan formula against a Chern root collapses to two terms. -/
theorem sq_mul_y (k : σ) (u : A) (n : ℕ) :
    D.Sq n (D.y k * u) = D.y k * D.Sq n u + D.y k ^ 2 * D.sqShift n u := by
  rcases n with _ | _ | n
  · show D.Sq 0 (D.y k * u) = D.y k * D.Sq 0 u + D.y k ^ 2 * D.sqShift 0 u
    simp [D.sq_zero_apply]
  · show D.Sq 1 (D.y k * u) = D.y k * D.Sq 1 u + D.y k ^ 2 * D.sqShift 1 u
    rw [D.cartan 1 (D.y k) u]
    simp [Finset.sum_range_succ, D.sq_zero_apply, D.sq_y_one]
  · show D.Sq (n + 2) (D.y k * u) = D.y k * D.Sq (n + 2) u + D.y k ^ 2 * D.sqShift (n + 2) u
    rw [D.cartan (n + 2) (D.y k) u]
    have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (n + 2 + 1) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_range]
      rcases hp with rfl | rfl <;> omega
    have hzero : ∀ p ∈ Finset.range (n + 2 + 1), p ∉ ({0, 2} : Finset ℕ) →
        D.Sq p (D.y k) * D.Sq (n + 2 - p) u = 0 := by
      intro p _ hp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      have hzp : D.Sq p (D.y k) = 0 := by
        rcases p with _ | p
        · exact absurd rfl hp.1
        · rcases p with _ | p
          · exact D.sq_y_one k
          · rcases p with _ | p
            · exact absurd rfl hp.2
            · exact D.sq_y_high k _ (by omega)
      rw [hzp, zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2),
      Nat.sub_zero, show n + 2 - 2 = n from by omega, D.sq_zero_apply, D.sq_y_two,
      sqShift_add_two]

/-- `Sq^n 1 = 0` for `n > 0`, from the Cartan formula and `Sq^0 = id`. -/
theorem sq_one_eq_zero : ∀ n : ℕ, 0 < n → D.Sq n 1 = 0 := by
  suffices H : ∀ N n : ℕ, n ≤ N → 0 < n → D.Sq n 1 = 0 by
    intro n hn
    exact H n n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro n hnN hpos
    omega
  | succ N ihN =>
    intro n hnN hpos
    have hcar : D.Sq n ((1 : A) * 1)
        = ∑ p ∈ Finset.range (n + 1), D.Sq p 1 * D.Sq (n - p) 1 := D.cartan n 1 1
    rw [one_mul] at hcar
    have hsub : ({0, n} : Finset ℕ) ⊆ Finset.range (n + 1) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_range]
      rcases hp with rfl | rfl <;> omega
    have hzero : ∀ p ∈ Finset.range (n + 1), p ∉ ({0, n} : Finset ℕ) →
        D.Sq p 1 * D.Sq (n - p) 1 = 0 := by
      intro p hp hp'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
      have hplt : p < n := by
        have hpr := Finset.mem_range.mp hp
        omega
      have hpos' : 0 < p := Nat.pos_of_ne_zero hp'.1
      rw [ihN p (by omega) hpos', zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0 : ℕ) ≠ n),
      Nat.sub_zero, Nat.sub_self, D.sq_zero_apply, one_mul, mul_one] at hcar
    calc D.Sq n 1 = D.Sq n 1 + D.Sq n 1 := hcar
      _ = 0 := add_self_eq_zero_of_two_eq_zero D.two_eq_zero _

/-- `Sq^{2c}` of a squarefree monomial squares `c` of its factors; the odd squares
vanish. -/
theorem sq_prod [DecidableEq σ] (C : Finset σ) :
    ∀ c : ℕ, D.Sq (2 * c) (∏ l ∈ C, D.y l) = wuMonomialOn C D.y c
      ∧ D.Sq (2 * c + 1) (∏ l ∈ C, D.y l) = 0 := by
  refine Finset.induction_on C ?_ ?_
  · intro c
    rw [Finset.prod_empty]
    cases c with
    | zero =>
      refine ⟨?_, ?_⟩
      · show D.Sq 0 (1 : A) = wuMonomialOn (∅ : Finset σ) D.y 0
        rw [D.sq_zero_apply, wuMonomialOn_zero, Finset.prod_empty]
      · show D.Sq 1 (1 : A) = 0
        exact D.sq_one_eq_zero 1 (by omega)
    | succ c' =>
      refine ⟨?_, ?_⟩
      · show D.Sq (2 * c' + 2) (1 : A) = wuMonomialOn (∅ : Finset σ) D.y (c' + 1)
        rw [D.sq_one_eq_zero (2 * c' + 2) (by omega),
          wuMonomialOn_empty_of_pos D.y (show 0 < c' + 1 by omega)]
      · show D.Sq (2 * c' + 3) (1 : A) = 0
        exact D.sq_one_eq_zero (2 * c' + 3) (by omega)
  · intro w t hw ih c
    rw [Finset.prod_insert hw]
    cases c with
    | zero =>
      refine ⟨?_, ?_⟩
      · show D.Sq 0 (D.y w * ∏ l ∈ t, D.y l) = wuMonomialOn (insert w t) D.y 0
        rw [D.sq_zero_apply, wuMonomialOn_zero, Finset.prod_insert hw]
      · have h0 : D.Sq 1 (∏ l ∈ t, D.y l) = 0 := (ih 0).2
        show D.Sq 1 (D.y w * ∏ l ∈ t, D.y l) = 0
        rw [D.sq_mul_y, sqShift_one, mul_zero, add_zero, h0, mul_zero]
    | succ c' =>
      have ih1 : D.Sq (2 * c' + 2) (∏ l ∈ t, D.y l) = wuMonomialOn t D.y (c' + 1) :=
        (ih (c' + 1)).1
      have ih2 : D.Sq (2 * c') (∏ l ∈ t, D.y l) = wuMonomialOn t D.y c' := (ih c').1
      have ih3 : D.Sq (2 * c' + 1 + 2) (∏ l ∈ t, D.y l) = 0 := (ih (c' + 1)).2
      have ih4 : D.Sq (2 * c' + 1) (∏ l ∈ t, D.y l) = 0 := (ih c').2
      refine ⟨?_, ?_⟩
      · show D.Sq (2 * c' + 2) (D.y w * ∏ l ∈ t, D.y l)
            = wuMonomialOn (insert w t) D.y (c' + 1)
        rw [D.sq_mul_y, sqShift_add_two, ih1, ih2, wuMonomialOn_insert hw]
      · show D.Sq (2 * c' + 3) (D.y w * ∏ l ∈ t, D.y l) = 0
        rw [show 2 * c' + 3 = 2 * c' + 1 + 2 from by omega, D.sq_mul_y, sqShift_add_two,
          ih3, ih4, mul_zero, mul_zero, add_zero]

/-- The `j`-th mod-2 Chern class of the split family. -/
def gamma (j : ℕ) : A := esymmOn D.s D.y j

theorem gamma_def (j : ℕ) : D.gamma j = esymmOn D.s D.y j := rfl

@[simp] theorem gamma_zero : D.gamma 0 = 1 := esymmOn_zero _ _

theorem sq_gamma_succ [DecidableEq σ] (i : ℕ) :
    D.Sq (2 * i) (D.gamma (i + 1))
      = ∑ C ∈ D.s.powersetCard (i + 1), wuMonomialOn C D.y i := by
  rw [gamma_def, esymmOn_def, map_sum]
  exact Finset.sum_congr rfl fun C _ => (D.sq_prod C i).1

/-- **(Wu-diag).**  `Sq^{2i} γ_{i+1} = ∑_{j ≤ i} γ_{i-j} γ_{i+1+j}`. -/
theorem wu_diagonal [DecidableEq σ] (i : ℕ) :
    D.Sq (2 * i) (D.gamma (i + 1))
      = ∑ j ∈ Finset.range (i + 1), D.gamma (i - j) * D.gamma (i + 1 + j) := by
  have h1 : ∑ j ∈ Finset.range (i + 1), D.gamma (i - j) * D.gamma (i + 1 + j)
      = esymmWuRHS D.s D.y i := esymm_halfAntidiagonal_eq D.two_eq_zero D.s D.y i
  rw [h1, esymmWuRHS_eq_sum_powersetCard_succ]
  exact D.sq_gamma_succ i

end SqData

end GroupApproximation.CharClass
