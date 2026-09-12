import GroupApproximation.CharClass.ParityPData
import GroupApproximation.CharClass.WuSymmetric

/-!
# The Cartan half of the diagonal Wu relation at a general prime

This is the first of the two halves of `sp-design`'s L4a, and the easy one.  Over an
abstract commutative ring with a total reduced power `P` satisfying `P^0 = id`, the Cartan
formula, and `P(y) = y + κ·y^p` on the Chern roots, it computes

```text
P^i( e_{i+1}(y) )  =  κ^i · ∑_{|B| = i} ∑_{k ∈ s \ B} (∏_{l ∈ B} y_l^p) · y_k .
```

The right-hand side is the monomial symmetric function `m_{(p^i,1)}(y)`, scaled by `κ^i`.
Turning it into `c_i · e_{ip+1}(y) + (decomposables)` is the second half, which needs
Newton's identities and the fundamental theorem of symmetric polynomials, and lives in a
separate module.

## Relation to the `F₂` tree

This is `CharClass/WuDiagonal.lean` with three changes, and it is deliberately written so
that the `F₂` file could be recovered by instantiating `p = 2`, `κ = 1`:

* `SqData`'s `Sq^1 y = 0`, `Sq^2 y = y²`, `Sq^{≥3} y = 0` become `P^1 y = κ·y^p` and
  `P^{≥2} y = 0`.  The mod-2 file indexes by the cohomological degree, so its operation
  jumps by two and it must carry the vanishing of the odd squares through the induction;
  here the index *is* the number of factors that get raised to the `p`-th power, so there
  is no parity bookkeeping at all and `p_prod` is a single statement rather than a
  conjunction.
* `SqData` assumes `(2 : A) = 0`, and uses it exactly once, to derive `Sq^n 1 = 0` from
  `Sq^n 1 = 2·Sq^n 1`.  That step needs no characteristic hypothesis — `x = x + x` gives
  `x = 0` in any additive group — so `PowerData` asks for no characteristic at all.
* `wuMonomialOn` hard-codes the factor `y_l ^ 2`.  `wuMonomialP` takes the replacement
  `g : σ → A` as a parameter.  Nothing in the subset combinatorics ever looks at it, and
  the generality is what lets the same reindexing serve `p = 2` and odd `p`.

`wuMonomialP` and `WuDiagonal.wuMonomialOn` are therefore the same combinatorics twice.
They are not shared because `WuSymmetric.lean` and `WuDiagonal.lean` belong to the mod-2
answer, which is a verified artifact that this program does not edit; if the lead later
wants them merged, `wuMonomialOn C y c = wuMonomialP C (fun l => y l ^ 2) y c` by `rfl`.

## Main results

* `GroupApproximation.CharClass.ParityP.PowerData` — the hypotheses, as a structure.
* `ParityP.PowerData.p_prod` — `P^c` of a squarefree monomial.
* `ParityP.wuRHSP_eq_sum_wuMonomialP` — the two shapes of the right-hand side.
* `ParityP.PowerData.p_gamma_succ` — `P^i(e_{i+1}(y))` as a sum over subsets.
* `ParityP.PowerData.p_gamma_succ_eq_smul` — the same, as `κ^i · m_{(p^i,1)}(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open Finset

/-! ## 1. `P^c` of a squarefree monomial, as a sum over subsets -/

section Monomial

variable {σ A : Type*} [CommRing A] [DecidableEq σ]

/-- `wuMonomialP C g y c` is what `P^c` produces from the squarefree monomial
`∏_{l ∈ C} y_l`: choose `c` of the factors and replace each of them by `g l`.  For the
reduced powers `g l = κ · y_l ^ p`; nothing below uses that. -/
def wuMonomialP (C : Finset σ) (g y : σ → A) (c : ℕ) : A :=
  ∑ B ∈ C.powersetCard c, (∏ l ∈ B, g l) * ∏ l ∈ C \ B, y l

theorem wuMonomialP_def (C : Finset σ) (g y : σ → A) (c : ℕ) :
    wuMonomialP C g y c = ∑ B ∈ C.powersetCard c, (∏ l ∈ B, g l) * ∏ l ∈ C \ B, y l := rfl

theorem wuMonomialP_zero (C : Finset σ) (g y : σ → A) :
    wuMonomialP C g y 0 = ∏ l ∈ C, y l := by
  rw [wuMonomialP_def, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty,
    Finset.sdiff_empty, one_mul]

theorem wuMonomialP_empty_of_pos (g y : σ → A) {c : ℕ} (hc : 0 < c) :
    wuMonomialP (∅ : Finset σ) g y c = 0 := by
  have h : (∅ : Finset σ).powersetCard c = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hc)
  rw [wuMonomialP_def, h, Finset.sum_empty]

/-- Adjoining a variable: the new factor is either left alone or replaced by `g w`. -/
theorem wuMonomialP_insert {w : σ} {C : Finset σ} (hw : w ∉ C) (g y : σ → A) (c : ℕ) :
    wuMonomialP (insert w C) g y (c + 1)
      = y w * wuMonomialP C g y (c + 1) + g w * wuMonomialP C g y c := by
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
        (∏ l ∈ B, g l) * ∏ l ∈ insert w C \ B, y l
      = y w * wuMonomialP C g y (c + 1) := by
    rw [wuMonomialP_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hBC : B ⊆ C := (Finset.mem_powersetCard.mp hB).1
    have hwB : w ∉ B := fun h => hw (hBC h)
    have hwCB : w ∉ C \ B := by
      simp only [Finset.mem_sdiff, not_and]
      exact fun h => absurd h hw
    rw [Finset.insert_sdiff_of_notMem C hwB, Finset.prod_insert hwCB]
    ring
  have hblock2 : ∑ B ∈ (C.powersetCard c).image (insert w),
        (∏ l ∈ B, g l) * ∏ l ∈ insert w C \ B, y l
      = g w * wuMonomialP C g y c := by
    rw [Finset.sum_image hinj, wuMonomialP_def, Finset.mul_sum]
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
  calc wuMonomialP (insert w C) g y (c + 1)
      = (∑ B ∈ C.powersetCard (c + 1), (∏ l ∈ B, g l) * ∏ l ∈ insert w C \ B, y l)
        + ∑ B ∈ (C.powersetCard c).image (insert w),
            (∏ l ∈ B, g l) * ∏ l ∈ insert w C \ B, y l := by
        rw [wuMonomialP_def, hps]
        exact Finset.sum_union hdisj
    _ = y w * wuMonomialP C g y (c + 1) + g w * wuMonomialP C g y c := by
        rw [hblock1, hblock2]

/-! ### The two shapes of the right-hand side -/

/-- The right-hand side of the Wu identity: over all `i`-element subsets `B` of the index
set and all indices `k` outside `B`, the monomial `(∏_{l ∈ B} g l) · y_k`.  At
`g l = y_l ^ p` this is the monomial symmetric function `m_{(p^i,1)}(y)`. -/
def wuRHSP (s : Finset σ) (g y : σ → A) (i : ℕ) : A :=
  ∑ B ∈ s.powersetCard i, ∑ k ∈ s \ B, (∏ l ∈ B, g l) * y k

theorem wuRHSP_def (s : Finset σ) (g y : σ → A) (i : ℕ) :
    wuRHSP s g y i = ∑ B ∈ s.powersetCard i, ∑ k ∈ s \ B, (∏ l ∈ B, g l) * y k := rfl

/-- The datum of a set `B ⊆ s` of size `i` together with an index `k ∈ s \ B` is the datum
of a set `C ⊆ s` of size `i + 1` together with a subset `B ⊆ C` of size `i`, under
`C = insert k B`.

This is `WuSymmetric.esymmWuRHS_eq_sum_powersetCard_succ` with the factor `y_l ^ 2`
replaced by an arbitrary `g l`; the bijection never looks at the factor, which is the whole
reason the mod-2 combinatorics transfers to an arbitrary prime unchanged. -/
theorem wuRHSP_eq_sum_wuMonomialP (s : Finset σ) (g y : σ → A) (i : ℕ) :
    wuRHSP s g y i = ∑ C ∈ s.powersetCard (i + 1), wuMonomialP C g y i := by
  have hsdiff : ∀ (B : Finset σ) (k : σ), k ∉ B → insert k B \ B = {k} := by
    intro B k hk
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact hx
      · exact absurd hx hx'
    · rintro rfl
      exact ⟨Or.inl rfl, hk⟩
  simp only [wuRHSP_def, wuMonomialP_def]
  rw [Finset.sum_sigma' (s.powersetCard i) (fun B => s \ B)
      (fun B k => (∏ l ∈ B, g l) * y k),
    Finset.sum_sigma' (s.powersetCard (i + 1)) (fun C => C.powersetCard i)
      (fun C B => (∏ l ∈ B, g l) * ∏ l ∈ C \ B, y l)]
  refine Finset.sum_bij
    (fun z _ => (⟨insert z.2 z.1, z.1⟩ : (_ : Finset σ) × Finset σ)) ?_ ?_ ?_ ?_
  · rintro ⟨B, k⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hz ⊢
    obtain ⟨⟨hBs, hBc⟩, hks, hkB⟩ := hz
    exact ⟨⟨Finset.insert_subset hks hBs, by rw [Finset.card_insert_of_notMem hkB, hBc]⟩,
      Finset.subset_insert _ _, hBc⟩
  · rintro ⟨B, k⟩ hz ⟨B', k'⟩ _ heq
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at hz
    have hBB : B = B' := congrArg (fun z : (_ : Finset σ) × Finset σ => z.2) heq
    have hins : insert k B = insert k' B' :=
      congrArg (fun z : (_ : Finset σ) × Finset σ => z.1) heq
    subst hBB
    have hkmem : k ∈ insert k' B := by rw [← hins]; exact Finset.mem_insert_self k B
    rcases Finset.mem_insert.mp hkmem with h | h
    · subst h; rfl
    · exact absurd h hz.2.2
  · rintro ⟨C, B⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hz
    obtain ⟨⟨hCs, hCc⟩, hBC, hBc⟩ := hz
    have hnsub : ¬ (C ⊆ B) := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      omega
    obtain ⟨k, hkC, hkB⟩ := Finset.not_subset.mp hnsub
    have hins : insert k B = C := by
      refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hkC hBC) ?_
      rw [Finset.card_insert_of_notMem hkB, hBc, hCc]
    refine ⟨⟨B, k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff]
      exact ⟨⟨hBC.trans hCs, hBc⟩, hCs hkC, hkB⟩
    · simp only [hins]
  · rintro ⟨B, k⟩ hz
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at hz
    show (∏ l ∈ B, g l) * y k = (∏ l ∈ B, g l) * ∏ l ∈ insert k B \ B, y l
    rw [hsdiff B k hz.2.2, Finset.prod_singleton]

end Monomial

/-! ## 2. The abstract reduced-power data -/

/-- Exactly the facts the diagonal Wu relation is derived from at the prime `p`: a
commutative ring, an additive operation `P` with `P^0 = id` and the Cartan formula, and a
finite family `y` of degree-two classes with `P(y) = y + κ·y^p`.

No characteristic hypothesis, and no primality: `p` and `κ` are a natural number and a ring
element, and the computation below is an identity of formal sums over subsets. -/
structure PowerData (σ : Type*) (A : Type*) [CommRing A] (p : ℕ) where
  /-- The reduced powers, additive in the class. -/
  P : ℕ → A →+ A
  /-- `P^0` is the identity. -/
  p_zero_apply : ∀ a : A, P 0 a = a
  /-- The Cartan formula. -/
  cartan : ∀ (n : ℕ) (u v : A),
    P n (u * v) = ∑ j ∈ Finset.range (n + 1), P j u * P (n - j) v
  /-- The index set of the Chern roots. -/
  s : Finset σ
  /-- The Chern roots, of cohomological degree two. -/
  y : σ → A
  /-- The normalisation constant of the degree-two relation `P(h) = h + κ·h^p`.  It is `1`
  at `p = 2`, and a unit that nobody intends to pin at odd `p`. -/
  κ : A
  /-- `P^1` on a degree-two class is `κ` times its `p`-th power. -/
  p_y_one : ∀ k : σ, P 1 (y k) = κ * y k ^ p
  /-- Instability for a degree-two class: `P^j` vanishes on it for `j ≥ 2`. -/
  p_y_high : ∀ (k : σ) (j : ℕ), 2 ≤ j → P j (y k) = 0

namespace PowerData

variable {σ A : Type*} [CommRing A] {p : ℕ} (D : PowerData σ A p)

/-- `P` shifted down by one: the coefficient of `κ·y_k^p` in the Cartan expansion of
`P^n (y_k · u)`. -/
def pShift : ℕ → A → A
  | 0, _ => 0
  | (n + 1), u => D.P n u

@[simp] theorem pShift_zero (u : A) : D.pShift 0 u = 0 := rfl

@[simp] theorem pShift_succ (n : ℕ) (u : A) : D.pShift (n + 1) u = D.P n u := rfl

/-- The Cartan formula against a Chern root collapses to two terms. -/
theorem p_mul_y (k : σ) (u : A) (n : ℕ) :
    D.P n (D.y k * u) = D.y k * D.P n u + D.κ * D.y k ^ p * D.pShift n u := by
  cases n with
  | zero =>
    show D.P 0 (D.y k * u) = D.y k * D.P 0 u + D.κ * D.y k ^ p * D.pShift 0 u
    rw [D.p_zero_apply, D.p_zero_apply, pShift_zero, mul_zero, add_zero]
  | succ n =>
    show D.P (n + 1) (D.y k * u)
        = D.y k * D.P (n + 1) u + D.κ * D.y k ^ p * D.pShift (n + 1) u
    rw [D.cartan (n + 1) (D.y k) u]
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1 + 1) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_range]
      rcases hj with rfl | rfl <;> omega
    have hzero : ∀ j ∈ Finset.range (n + 1 + 1), j ∉ ({0, 1} : Finset ℕ) →
        D.P j (D.y k) * D.P (n + 1 - j) u = 0 := by
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have hzj : D.P j (D.y k) = 0 := by
        rcases j with _ | j
        · exact absurd rfl hj.1
        · rcases j with _ | j
          · exact absurd rfl hj.2
          · exact D.p_y_high k _ (by omega)
      rw [hzj, zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0 : ℕ) ≠ 1),
      Nat.sub_zero, Nat.add_sub_cancel, D.p_zero_apply, D.p_y_one, pShift_succ]

/-- `P^n 1 = 0` for `n > 0`, from the Cartan formula and `P^0 = id`.  No characteristic
hypothesis: `x = x + x` gives `x = 0` in any additive group. -/
theorem p_one_eq_zero : ∀ n : ℕ, 0 < n → D.P n 1 = 0 := by
  suffices H : ∀ N n : ℕ, n ≤ N → 0 < n → D.P n 1 = 0 by
    intro n hn
    exact H n n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro n hnN hpos
    omega
  | succ N ihN =>
    intro n hnN hpos
    have hcar : D.P n ((1 : A) * 1)
        = ∑ j ∈ Finset.range (n + 1), D.P j 1 * D.P (n - j) 1 := D.cartan n 1 1
    rw [one_mul] at hcar
    have hsub : ({0, n} : Finset ℕ) ⊆ Finset.range (n + 1) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_range]
      rcases hj with rfl | rfl <;> omega
    have hzero : ∀ j ∈ Finset.range (n + 1), j ∉ ({0, n} : Finset ℕ) →
        D.P j 1 * D.P (n - j) 1 = 0 := by
      intro j hj hj'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
      have hjlt : j < n := by
        have := Finset.mem_range.mp hj
        omega
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj'.1
      rw [ihN j (by omega) hjpos, zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0 : ℕ) ≠ n),
      Nat.sub_zero, Nat.sub_self, D.p_zero_apply, one_mul, mul_one] at hcar
    have h0 : (0 : A) + D.P n 1 = D.P n 1 + D.P n 1 := by rw [zero_add]; exact hcar
    exact (add_right_cancel h0).symm

/-- **`P^c` of a squarefree monomial** raises exactly `c` of its factors to the `p`-th
power, each contributing a factor `κ`. -/
theorem p_prod [DecidableEq σ] (C : Finset σ) :
    ∀ c : ℕ, D.P c (∏ l ∈ C, D.y l)
      = wuMonomialP C (fun l => D.κ * D.y l ^ p) D.y c := by
  refine Finset.induction_on C ?_ ?_
  · intro c
    rw [Finset.prod_empty]
    cases c with
    | zero =>
      show D.P 0 (1 : A) = wuMonomialP (∅ : Finset σ) _ D.y 0
      rw [D.p_zero_apply, wuMonomialP_zero, Finset.prod_empty]
    | succ c =>
      show D.P (c + 1) (1 : A) = wuMonomialP (∅ : Finset σ) _ D.y (c + 1)
      rw [D.p_one_eq_zero (c + 1) (by omega),
        wuMonomialP_empty_of_pos _ D.y (show 0 < c + 1 by omega)]
  · intro w C hw ih c
    rw [Finset.prod_insert hw]
    cases c with
    | zero =>
      show D.P 0 (D.y w * ∏ l ∈ C, D.y l) = wuMonomialP (insert w C) _ D.y 0
      rw [D.p_zero_apply, wuMonomialP_zero, Finset.prod_insert hw]
    | succ c =>
      show D.P (c + 1) (D.y w * ∏ l ∈ C, D.y l) = wuMonomialP (insert w C) _ D.y (c + 1)
      rw [D.p_mul_y, pShift_succ, ih (c + 1), ih c, wuMonomialP_insert hw]

/-- The `j`-th Chern class of the split family. -/
def gamma (j : ℕ) : A := esymmOn D.s D.y j

theorem gamma_def (j : ℕ) : D.gamma j = esymmOn D.s D.y j := rfl

@[simp] theorem gamma_zero : D.gamma 0 = 1 := esymmOn_zero _ _

/-- **The Cartan half of L4a.**  `P^i` of the `(i+1)`-st Chern class is the sum, over the
`(i+1)`-element subsets, of the ways to raise `i` of the factors to the `p`-th power. -/
theorem p_gamma_succ [DecidableEq σ] (i : ℕ) :
    D.P i (D.gamma (i + 1))
      = ∑ C ∈ D.s.powersetCard (i + 1), wuMonomialP C (fun l => D.κ * D.y l ^ p) D.y i := by
  rw [gamma_def, esymmOn_def, map_sum]
  exact Finset.sum_congr rfl fun C _ => D.p_prod C i

/-- **The Cartan half of L4a.**  `P^i` of the `(i+1)`-st Chern class is `κ^i` times the
monomial symmetric function `m_{(p^i,1)}(y)`.  Everything after this point is symmetric
functions and has no operation in it. -/
theorem p_gamma_succ_eq_smul [DecidableEq σ] (i : ℕ) :
    D.P i (D.gamma (i + 1)) = D.κ ^ i * wuRHSP D.s (fun l => D.y l ^ p) D.y i := by
  rw [D.p_gamma_succ i, ← wuRHSP_eq_sum_wuMonomialP, wuRHSP_def, wuRHSP_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hcard : B.card = i := (Finset.mem_powersetCard.mp hB).2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  ring

end PowerData

end ParityP

end GroupApproximation.CharClass
