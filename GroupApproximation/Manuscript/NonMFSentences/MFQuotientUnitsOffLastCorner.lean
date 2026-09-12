import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsCornerUnits
import GroupApproximation.Algebra.PeirceMatrixRing
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: `EL_{m-1}(T)` inside `(1-e_m)R(1-e_m) ≅ M_{m-1}(T)`

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1277–1280):

> Let `u ∈ ker κ` and write `u = gvh` as in (a).  The elementary matrices with `i, j ≤ m-1`
> form `EL_{m-1}(T)` inside `(1-e_m)R(1-e_m) ≅ M_{m-1}(T)`, so they lie in `N` by
> `eq:corner-units`; …

The census carrier of this clause (`MFQuotientUnitsSentences.manuscriptSentence_cornerUnitsLieInRadical`)
states `cornerUnitSubgroup R ≤ N` and constructs neither the corner `(1-e_m)R(1-e_m)` nor its
identification with `M_{m-1}(T)`.  This module builds both:

* `cornerMatrixEquiv`: for partial isometries `x_a ∈ e_a R p`, `y_a ∈ p R e_a` with
  `y_a x_b = δ_ab p`, the map `θ(A) = ∑ x_a A_ab y_b` is a ring isomorphism from the matrix
  ring over the corner `T = pRp` onto the corner at `∑ x_a y_a`;
* `manuscriptSentence_offLastCorner`: for an item-(a) decomposition `e_1, …, e_m` (indexed by
  `Fin (m + 1)`, the blocks off `last` by `last.succAbove : Fin m → Fin (m + 1)`, so that the
  printed `M_{m-1}(T)` is `Matrix (Fin m) (Fin m) T`), `θ` identifies `M_{m-1}(T)` with the
  corner at `P = 1 - e_last`; every root `1 + x`, `x ∈ e_i R e_j` with `i ≠ j` off `last`, is
  `1 - P + θ(e_{ij}(c))` for an elementary matrix `e_{ij}(c) ∈ EL_{m-1}(T)`; and it lies in
  `N = Rad_MF(Rˣ)` by `eq:corner-units`, since `T ≠ 0` (item (a)'s clause about `f` forces it).

Nothing is assumed.
-/

namespace GroupApproximation
namespace MFQuotientUnitsOffLastCorner

open MFQuotientUnits

section CornerEmbedding

variable {R : Type} [Ring R] {p : R} {n : ℕ} {x y : Fin n → R}

/-- **`θ(A) = ∑ a b, x a · A_ab · y b`** for a matrix over the corner `pRp`. -/
def cornerMatrixEmbed (hp : IsIdempotentElem p) (x y : Fin n → R)
    (A : Matrix (Fin n) (Fin n) (Corner R p hp)) : R :=
  ∑ a, ∑ b, x a * ((A a b : Corner R p hp) : R) * y b

/-- The idempotent `∑ a, x a · y a` that `θ` lands in the corner of. -/
def cornerWitnessSum (x y : Fin n → R) : R := ∑ a, x a * y a

theorem isIdempotentElem_cornerWitnessSum (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hxp : ∀ a, x a * p = x a) :
    IsIdempotentElem (cornerWitnessSum x y) := by
  show cornerWitnessSum x y * cornerWitnessSum x y = cornerWitnessSum x y
  have hstep : ∀ a b : Fin n, (x a * y a) * (x b * y b)
      = if a = b then x a * y a else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      have h1 : x a * y a * (x a * y a) = x a * (y a * x a) * y a := by noncomm_ring
      rw [h1, hyx a, hxp a]
    · rw [if_neg hab]
      have h1 : x a * y a * (x b * y b) = x a * (y a * x b) * y b := by noncomm_ring
      rw [h1, hcross a b hab, mul_zero, zero_mul]
  calc cornerWitnessSum x y * cornerWitnessSum x y
      = ∑ a, ∑ b, (x a * y a) * (x b * y b) := by
        unfold cornerWitnessSum; rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, (if a = b then x a * y a else 0) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b
    _ = ∑ a, x a * y a := Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_eq_single a (fun b _ hba => if_neg (Ne.symm hba))
          (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]
    _ = cornerWitnessSum x y := rfl

theorem cornerMatrixEmbed_add (hp : IsIdempotentElem p)
    (A B : Matrix (Fin n) (Fin n) (Corner R p hp)) :
    cornerMatrixEmbed hp x y (A + B) = cornerMatrixEmbed hp x y A + cornerMatrixEmbed hp x y B := by
  unfold cornerMatrixEmbed
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show x a * (((A + B) a b : Corner R p hp) : R) * y b =
    x a * ((A a b : Corner R p hp) : R) * y b + x a * ((B a b : Corner R p hp) : R) * y b
  rw [Matrix.add_apply, coe_corner_add, mul_add, add_mul]

theorem cornerMatrixEmbed_one (hxp : ∀ a, x a * p = x a) (hp : IsIdempotentElem p) :
    cornerMatrixEmbed hp x y (1 : Matrix (Fin n) (Fin n) (Corner R p hp)) =
      cornerWitnessSum x y := by
  unfold cornerMatrixEmbed cornerWitnessSum
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hba => by
      show x a * (((1 : Matrix (Fin n) (Fin n) (Corner R p hp)) a b : Corner R p hp) : R) *
        y b = 0
      rw [Matrix.one_apply_ne (Ne.symm hba), coe_corner_zero, mul_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h)]
  show x a * (((1 : Matrix (Fin n) (Fin n) (Corner R p hp)) a a : Corner R p hp) : R) * y a =
    x a * y a
  rw [Matrix.one_apply_eq, coe_cornerOne, hxp a]

theorem cornerMatrixEmbed_single (hp : IsIdempotentElem p) (a b : Fin n)
    (c : Corner R p hp) :
    cornerMatrixEmbed hp x y (Matrix.single a b c) = x a * (c : R) * y b := by
  unfold cornerMatrixEmbed
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Matrix.single_apply_same]
    · intro d _ hd
      rw [Matrix.single_apply_of_ne (h := fun h => hd h.2.symm), coe_corner_zero, mul_zero,
        zero_mul]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · intro d _ hd
    refine Finset.sum_eq_zero fun d' _ => ?_
    rw [Matrix.single_apply_of_ne (h := fun h => hd h.1.symm), coe_corner_zero, mul_zero,
      zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem cornerMatrixEmbed_mem (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hp : IsIdempotentElem p)
    (A : Matrix (Fin n) (Fin n) (Corner R p hp)) :
    cornerWitnessSum x y * cornerMatrixEmbed hp x y A = cornerMatrixEmbed hp x y A ∧
      cornerMatrixEmbed hp x y A * cornerWitnessSum x y = cornerMatrixEmbed hp x y A := by
  constructor
  · have hstep : ∀ c a b : Fin n, x c * y c * (x a * ((A a b : Corner R p hp) : R) * y b)
        = if c = a then x c * ((A a b : Corner R p hp) : R) * y b else 0 := by
      intro c a b
      by_cases hca : c = a
      · subst hca
        rw [if_pos rfl]
        have h1 : x c * y c * (x c * ((A c b : Corner R p hp) : R) * y b)
            = x c * ((y c * x c) * ((A c b : Corner R p hp) : R)) * y b := by noncomm_ring
        have hpA : p * ((A c b : Corner R p hp) : R) = ((A c b : Corner R p hp) : R) :=
          (A c b).2.1
        rw [h1, hyx c, hpA]
      · rw [if_neg hca]
        have h1 : x c * y c * (x a * ((A a b : Corner R p hp) : R) * y b)
            = x c * (y c * x a) * ((A a b : Corner R p hp) : R) * y b := by noncomm_ring
        rw [h1, hcross c a hca]
        simp
    unfold cornerWitnessSum cornerMatrixEmbed
    calc (∑ c, x c * y c) * ∑ a, ∑ b, x a * ((A a b : Corner R p hp) : R) * y b
        = ∑ c, ∑ a, ∑ b, x c * y c * (x a * ((A a b : Corner R p hp) : R) * y b) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by
              rw [Finset.mul_sum]
      _ = ∑ c, ∑ a, ∑ b, (if c = a then x c * ((A a b : Corner R p hp) : R) * y b else 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => hstep c a b
      _ = ∑ c, ∑ b, x c * ((A c b : Corner R p hp) : R) * y b :=
          Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_eq_single c
              (fun a _ hac =>
                (Finset.sum_congr rfl fun b _ => if_neg (fun h => hac h.symm)).trans
                  Finset.sum_const_zero)
              (fun h => absurd (Finset.mem_univ c) h)]
            exact Finset.sum_congr rfl fun b _ => by rw [if_pos rfl]
      _ = ∑ a, ∑ b, x a * ((A a b : Corner R p hp) : R) * y b := rfl
  · unfold cornerWitnessSum cornerMatrixEmbed
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    show (x a * ((A a b : Corner R p hp) : R) * y b) * ∑ c, x c * y c =
      x a * ((A a b : Corner R p hp) : R) * y b
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single b (fun c _ hcb => ?_) (fun h => absurd (Finset.mem_univ b) h)]
    · have h1 : (x a * ((A a b : Corner R p hp) : R) * y b) * (x b * y b)
          = x a * (((A a b : Corner R p hp) : R) * (y b * x b)) * y b := by noncomm_ring
      have hAp : ((A a b : Corner R p hp) : R) * p = ((A a b : Corner R p hp) : R) :=
        (A a b).2.2
      rw [h1, hyx b, hAp]
    · have h1 : (x a * ((A a b : Corner R p hp) : R) * y b) * (x c * y c)
          = x a * ((A a b : Corner R p hp) : R) * (y b * x c) * y c := by noncomm_ring
      rw [h1, hcross b c (Ne.symm hcb), mul_zero, zero_mul]

theorem cornerMatrixEmbed_mul (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hp : IsIdempotentElem p)
    (A B : Matrix (Fin n) (Fin n) (Corner R p hp)) :
    cornerMatrixEmbed hp x y (A * B) = cornerMatrixEmbed hp x y A * cornerMatrixEmbed hp x y B := by
  have hstep : ∀ i j k l : Fin n,
      (x i * ((A i j : Corner R p hp) : R) * y j) * (x k * ((B k l : Corner R p hp) : R) * y l)
        = if j = k then
            x i * (((A i j : Corner R p hp) : R) * ((B k l : Corner R p hp) : R)) * y l
          else 0 := by
    intro i j k l
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have h1 : (x i * ((A i j : Corner R p hp) : R) * y j) *
            (x j * ((B j l : Corner R p hp) : R) * y l)
          = x i * (((A i j : Corner R p hp) : R) * (y j * x j)) *
              ((B j l : Corner R p hp) : R) * y l := by noncomm_ring
      have hAp : ((A i j : Corner R p hp) : R) * p = ((A i j : Corner R p hp) : R) :=
        (A i j).2.2
      rw [h1, hyx j, hAp]
      noncomm_ring
    · rw [if_neg hjk]
      have h1 : (x i * ((A i j : Corner R p hp) : R) * y j) *
            (x k * ((B k l : Corner R p hp) : R) * y l)
          = x i * ((A i j : Corner R p hp) : R) * (y j * x k) *
              ((B k l : Corner R p hp) : R) * y l := by noncomm_ring
      rw [h1, hcross j k hjk]
      simp
  unfold cornerMatrixEmbed
  refine Eq.symm ?_
  calc (∑ i, ∑ j, x i * ((A i j : Corner R p hp) : R) * y j) *
        ∑ k, ∑ l, x k * ((B k l : Corner R p hp) : R) * y l
      = ∑ i, ∑ j, ∑ k, ∑ l, (x i * ((A i j : Corner R p hp) : R) * y j) *
          (x k * ((B k l : Corner R p hp) : R) * y l) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (if j = k then
          x i * (((A i j : Corner R p hp) : R) * ((B k l : Corner R p hp) : R)) * y l
        else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
            hstep i j k l
    _ = ∑ i, ∑ j, ∑ l,
          x i * (((A i j : Corner R p hp) : R) * ((B j l : Corner R p hp) : R)) * y l := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j
          (fun k _ hkj =>
            (Finset.sum_congr rfl fun l _ => if_neg (Ne.symm hkj)).trans
              Finset.sum_const_zero)
          (fun h => absurd (Finset.mem_univ j) h)]
        exact Finset.sum_congr rfl fun l _ => by rw [if_pos rfl]
    _ = ∑ i, ∑ l, x i * (((A * B) i l : Corner R p hp) : R) * y l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, MatrixUnitSystem.coe_corner_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coe_corner_mul]

/-- The printed ring homomorphism `θ : M_n(T) → corner`. -/
noncomputable def cornerMatrixHom (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hxp : ∀ a, x a * p = x a)
    (hp : IsIdempotentElem p) :
    Matrix (Fin n) (Fin n) (Corner R p hp) →+*
      Corner R (cornerWitnessSum x y) (isIdempotentElem_cornerWitnessSum hyx hcross hxp) where
  toFun A := ⟨cornerMatrixEmbed hp x y A, cornerMatrixEmbed_mem hyx hcross hp A⟩
  map_one' := corner_ext (cornerMatrixEmbed_one hxp hp)
  map_mul' A B := corner_ext (cornerMatrixEmbed_mul hyx hcross hp A B)
  map_zero' := corner_ext (by simp [cornerMatrixEmbed])
  map_add' A B := corner_ext (cornerMatrixEmbed_add hp A B)

/-- The matrix entries are recovered by `y_a · θ(A) · x_b`. -/
theorem y_mul_cornerMatrixEmbed_mul_x (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hp : IsIdempotentElem p)
    (A : Matrix (Fin n) (Fin n) (Corner R p hp)) (a b : Fin n) :
    y a * cornerMatrixEmbed hp x y A * x b = ((A a b : Corner R p hp) : R) := by
  calc y a * cornerMatrixEmbed hp x y A * x b
      = ∑ c, ∑ d, y a * x c * ((A c d : Corner R p hp) : R) * (y d * x b) := by
        unfold cornerMatrixEmbed
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        noncomm_ring
    _ = y a * x a * ((A a b : Corner R p hp) : R) * (y b * x b) := by
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · intro d _ hd
            rw [hcross d b hd, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ b) h
        · intro c _ hc
          refine Finset.sum_eq_zero fun d _ => ?_
          rw [hcross a c (Ne.symm hc), zero_mul, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ a) h
    _ = ((A a b : Corner R p hp) : R) := by
        have hpA : p * ((A a b : Corner R p hp) : R) = ((A a b : Corner R p hp) : R) :=
          (A a b).2.1
        have hAp : ((A a b : Corner R p hp) : R) * p = ((A a b : Corner R p hp) : R) :=
          (A a b).2.2
        rw [hyx a, hyx b, hpA, hAp]

theorem mem_corner_coord (hxp : ∀ a, x a * p = x a) (hpy : ∀ a, p * y a = y a)
    (hp : IsIdempotentElem p) (z : R) (a b : Fin n) :
    y a * z * x b ∈ cornerNonUnitalSubring p hp := by
  refine ⟨?_, ?_⟩
  · show p * (y a * z * x b) = y a * z * x b
    rw [← mul_assoc, ← mul_assoc, hpy a]
  · show y a * z * x b * p = y a * z * x b
    rw [mul_assoc, hxp b]

theorem cornerMatrixEmbed_coords (hxp : ∀ a, x a * p = x a) (hpy : ∀ a, p * y a = y a)
    (hp : IsIdempotentElem p) (z : R) :
    cornerMatrixEmbed hp x y
        (Matrix.of fun a b => (⟨y a * z * x b, mem_corner_coord hxp hpy hp z a b⟩ :
          Corner R p hp)) =
      cornerWitnessSum x y * z * cornerWitnessSum x y := by
  unfold cornerMatrixEmbed cornerWitnessSum
  rw [Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  show x a * (y a * z * x b) * y b = x a * y a * z * (x b * y b)
  noncomm_ring

/-- **The printed identification `corner ≅ M_n(T)`.** -/
noncomputable def cornerMatrixEquiv (hyx : ∀ a, y a * x a = p)
    (hcross : ∀ a b : Fin n, a ≠ b → y a * x b = 0) (hxp : ∀ a, x a * p = x a)
    (hpy : ∀ a, p * y a = y a) (hp : IsIdempotentElem p) :
    Matrix (Fin n) (Fin n) (Corner R p hp) ≃+*
      Corner R (cornerWitnessSum x y) (isIdempotentElem_cornerWitnessSum hyx hcross hxp) :=
  RingEquiv.ofBijective (cornerMatrixHom hyx hcross hxp hp)
    ⟨fun A B hAB => by
      ext a b
      apply corner_ext
      have h := congrArg (fun w : Corner R (cornerWitnessSum x y)
        (isIdempotentElem_cornerWitnessSum hyx hcross hxp) => y a * (w : R) * x b) hAB
      change y a * cornerMatrixEmbed hp x y A * x b = y a * cornerMatrixEmbed hp x y B * x b at h
      rwa [y_mul_cornerMatrixEmbed_mul_x hyx hcross hp, y_mul_cornerMatrixEmbed_mul_x hyx hcross hp]
        at h,
     fun w => ⟨Matrix.of fun a b =>
        (⟨y a * (w : R) * x b, mem_corner_coord hxp hpy hp (w : R) a b⟩ : Corner R p hp),
      corner_ext (by
        change cornerMatrixEmbed hp x y (Matrix.of fun a b =>
          (⟨y a * (w : R) * x b, mem_corner_coord hxp hpy hp (w : R) a b⟩ :
            Corner R p hp)) = (w : R)
        have hw1 : cornerWitnessSum x y * (w : R) = (w : R) := w.2.1
        have hw2 : (w : R) * cornerWitnessSum x y = (w : R) := w.2.2
        rw [cornerMatrixEmbed_coords hxp hpy hp, hw1, hw2])⟩⟩

end CornerEmbedding

/-- **Printed (tex 1277–1280), at the printed objects.**  For an item-(a) decomposition
`e_1, …, e_m` of a countable purely infinite simple ring (here `m + 1` blocks, `m ≥ 3`,
indexed by `Fin (m + 1)`, the blocks off `last` pairwise equivalent and `e_last` equivalent to
some `f ≤ e_{i₀}`): there is a ring isomorphism `θ : M_{m-1}(T) → PRP`, `T = e_{i₀}Re_{i₀}`,
`P = 1 - e_last` (the printed `M_{m-1}(T)` is `Matrix (Fin m) (Fin m) T`); every elementary
root `1 + x`, `x ∈ e_i R e_j`, `i ≠ j` off `last`, is `1 - P + θ(A)` for some
`A ∈ EL_{m-1}(T)`; and it lies in `N` by `eq:corner-units`. -/
def PrintedOffLastCorner : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ), 3 ≤ m → ∀ (e : Fin (m + 1) → R) (hidem : ∀ i, IsIdempotentElem (e i)),
      (∀ i j : Fin (m + 1), i ≠ j → e i * e j = 0) → (∑ i, e i = 1) →
      ∀ i₀ last : Fin (m + 1), i₀ ≠ last →
        (∀ i j : Fin (m + 1), i ≠ last → j ≠ last → IsEquivalentIdempotent R (e i) (e j)) →
        ∀ (f : R), IsIdempotentElem f → IdempotentLE f (e i₀) →
          IsEquivalentIdempotent R (e last) f →
          ∃ (P : R) (hP : IsIdempotentElem P)
            (θ : Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀)) ≃+* Corner R P hP),
            P = 1 - e last ∧
            ∀ i j : Fin (m + 1), i ≠ j → i ≠ last → j ≠ last → ∀ x : R, e i * x = x →
              x * e j = x → ∀ w : Rˣ, (w : R) = 1 + x →
                ∃ A ∈ elementaryGroup (Fin m) (Corner R (e i₀) (hidem i₀)),
                  (w : R) = 1 - P + ((θ (A : Matrix (Fin m) (Fin m)
                    (Corner R (e i₀) (hidem i₀))) : Corner R P hP) : R) ∧
                  w ∈ mfHomKernel Rˣ

theorem manuscriptSentence_offLastCorner : PrintedOffLastCorner := by
  intro R _ _ hR m hm e hidem horth hsum i₀ last hne hpair f _hfi hfle hlast
  haveI : IsSimpleRing R := hR.isSimpleRing
  have hi₀ne : e i₀ ≠ 0 := by
    intro hz
    have hnl : ∀ i, i ≠ last → e i = 0 := by
      intro i hil
      by_contra hne0
      exact ne_zero_of_isEquivalentIdempotent (hidem i) hne0 (hpair i i₀ hil hne) hz
    have hf0 : f = 0 := by
      have hmul : e i₀ * f = f := hfle.1
      rw [hz, zero_mul] at hmul
      exact hmul.symm
    have hlast0 : e last = 0 := by
      by_contra hne0
      exact ne_zero_of_isEquivalentIdempotent (hidem last) hne0 hlast hf0
    apply one_ne_zero (α := R)
    rw [← hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hil : i = last
    · rw [hil, hlast0]
    · exact hnl i hil
  have hequiv : ∀ a : Fin m, ∃ X Y : R, X * Y = e (last.succAbove a) ∧ Y * X = e i₀ ∧
      e (last.succAbove a) * X = X ∧ X * e i₀ = X ∧ e i₀ * Y = Y ∧
      Y * e (last.succAbove a) = Y := fun a =>
    exists_normalized_equivalence (hidem _) (hidem i₀)
      (hpair _ i₀ (Fin.succAbove_ne last a) hne)
  choose x y hxy hyx hex hxe hey hye using hequiv
  have hcross : ∀ a b : Fin m, a ≠ b → y a * x b = 0 := by
    intro a b hab
    have hsab : last.succAbove a ≠ last.succAbove b :=
      fun h => hab (Fin.succAbove_right_injective h)
    calc y a * x b = (y a * e (last.succAbove a)) * (e (last.succAbove b) * x b) := by
          rw [hye, hex]
      _ = y a * (e (last.succAbove a) * e (last.succAbove b)) * x b := by noncomm_ring
      _ = 0 := by rw [horth _ _ hsab]; simp
  have hQ : cornerWitnessSum x y = 1 - e last := by
    have h1 : ∑ i, e i = e last + ∑ a : Fin m, e (last.succAbove a) :=
      Fin.sum_univ_succAbove e last
    unfold cornerWitnessSum
    rw [Finset.sum_congr rfl fun a _ => hxy a, eq_sub_iff_add_eq, add_comm, ← h1, hsum]
  have hP : IsIdempotentElem (cornerWitnessSum x y) :=
    isIdempotentElem_cornerWitnessSum hyx hcross hxe
  refine ⟨cornerWitnessSum x y, hP, cornerMatrixEquiv hyx hcross hxe hey (hidem i₀), hQ, ?_⟩
  intro i j hij hil hjl z hiz hzj w hw
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hil
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hjl
  have hab : a ≠ b := fun h => hij (by rw [h])
  let c : Corner R (e i₀) (hidem i₀) := ⟨y a * z * x b, mem_corner_coord hxe hey (hidem i₀) z a b⟩
  have hval : cornerMatrixEmbed (hidem i₀) x y
      (elementaryUnit a b hab c : Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀))) =
        cornerWitnessSum x y + z := by
    change cornerMatrixEmbed (hidem i₀) x y (1 + Matrix.single a b c) = _
    rw [cornerMatrixEmbed_add, cornerMatrixEmbed_one hxe, cornerMatrixEmbed_single]
    congr 1
    calc x a * (y a * z * x b) * y b = (x a * y a) * z * (x b * y b) := by noncomm_ring
      _ = z := by rw [hxy, hxy, hiz, hzj]
  have hkill : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (φ : elementaryGroup (Fin m) (Corner R (e i₀) (hidem i₀)) →* M)
        (g : elementaryGroup (Fin m) (Corner R (e i₀) (hidem i₀))), φ g = 1 :=
    fun M _ hM φ g =>
      (MFQuotientUnitsCornerUnits.manuscriptSentence_cornerRing R hR (e i₀) (hidem i₀)
        hi₀ne).2.2.2 m (by omega) M hM φ g
  have hunit : MFQuotientUnitsCornerUnits.cornerUnitsHom (hidem i₀) hP
      (cornerMatrixEquiv hyx hcross hxe hey (hidem i₀))
      ⟨elementaryUnit a b hab c, elementaryUnit_mem a b hab c⟩ = w := by
    apply Units.ext
    show 1 - cornerWitnessSum x y + cornerMatrixEmbed (hidem i₀) x y
      (elementaryUnit a b hab c : Matrix (Fin m) (Fin m) (Corner R (e i₀) (hidem i₀))) =
        (w : R)
    rw [hval, hw]
    abel
  refine ⟨elementaryUnit a b hab c, elementaryUnit_mem a b hab c, ?_, ?_⟩
  · rw [← hunit]
    rfl
  · rw [← hunit]
    exact range_le_mfHomKernel _ hkill ⟨_, rfl⟩

end MFQuotientUnitsOffLastCorner
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.isIdempotentElem_cornerWitnessSum
#audit_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.cornerMatrixEmbed_mul
#audit_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.y_mul_cornerMatrixEmbed_mul_x
#audit_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.cornerMatrixEmbed_coords
#audit_closed_axioms GroupApproximation.MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner
