import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalSubshiftPeriodicWord
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The periodic sequences `y_ℓ` and their least periods

`simple_kazhdan_sofic_group.tex` at e80dcf20a, "Finite models", tex 124–132:

> Since $x_{[m,m+2\ell)}=x_{[0,2\ell)}$, the $m$-periodic sequence $y_\ell$ that agrees with $x$ on
> $[0,m)$ agrees with $x$ on $[0,m+2\ell)$. Every window of length $2\ell+1$ of $y_\ell$ is a
> translate, by a multiple of $m$, of a window starting in $[0,m)$, and every word of $X$ of this
> length starts at some position in $[0,m)$. So $y_\ell$ has the same words of length $2\ell+1$ as
> $X$. Let $N_\ell$ be the least period of $y_\ell$. Then $N_\ell$ is at least the number of these
> words, which tends to infinity with $\ell$, since a subshift with boundedly many words of each
> length is finite.

Setting as in `MinimalSubshiftPeriodicWord`: `A` finite, `X ⊆ A^ℤ` shift-invariant, with chain-words'
`word` and `language`.

* `periodicExt x m`: the `m`-periodic sequence agreeing with `x` on `[0, m)`;
  `periodicExt_eq_of_lt`: it agrees with `x` on `[0, m + 2ℓ)`;
  `word_periodicExt_emod`: every window is a translate, by a multiple of `m`, of a window starting in
  `[0, m)`; `language_periodicExt`: the same words of length `2ℓ + 1` as `X`.
* `leastPeriod y`: the minimal period of `y` under the shift; `ncard_language_le_leastPeriod`: at
  least the number of words.
* `ncard_language_mono`, `finite_of_ncard_language_le`: word counts are monotone, and boundedly many
  words of each length force a finite subshift (equal consecutive counts give unique extensions to
  both sides, so a single window determines the point); `tendsto_ncard_language`: for an infinite
  subshift the counts tend to infinity.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift WordGraph Filter

variable {A : Type*}

/-! ### Word counts -/

theorem ncard_language_le_succ [Finite A] (X : Set (ℤ → A)) (n : ℕ) :
    (language X n).ncard ≤ (language X (n + 1)).ncard := by
  have hsub : language X n ⊆ (fun w : Fin (n + 1) → A => Fin.init w) '' language X (n + 1) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨word x 0 (n + 1), ⟨x, hx, rfl⟩, init_word x 0 n⟩
  exact (Set.ncard_le_ncard hsub).trans Set.ncard_image_le

theorem ncard_language_mono [Finite A] (X : Set (ℤ → A)) {m n : ℕ} (h : m ≤ n) :
    (language X m).ncard ≤ (language X n).ncard := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (ncard_language_le_succ X n)

theorem injOn_init_of_ncard_eq [Finite A] (X : Set (ℤ → A)) {n : ℕ}
    (heq : (language X (n + 1)).ncard = (language X n).ncard) :
    Set.InjOn (fun w : Fin (n + 1) → A => Fin.init w) (language X (n + 1)) := by
  have himg : (fun w : Fin (n + 1) → A => Fin.init w) '' language X (n + 1) = language X n := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact init_mem_language hw
    · rintro ⟨x, hx, rfl⟩
      exact ⟨word x 0 (n + 1), ⟨x, hx, rfl⟩, init_word x 0 n⟩
  exact (Set.ncard_image_iff (Set.toFinite _)).1 (by rw [himg, heq])

theorem injOn_tail_of_ncard_eq [Finite A] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) {n : ℕ}
    (heq : (language X (n + 1)).ncard = (language X n).ncard) :
    Set.InjOn (fun w : Fin (n + 1) → A => Fin.tail w) (language X (n + 1)) := by
  have himg : (fun w : Fin (n + 1) → A => Fin.tail w) '' language X (n + 1) = language X n := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact tail_mem_language hX hw
    · rintro ⟨x, hx, rfl⟩
      refine ⟨word x (-1) (n + 1), word_mem_language hX hx _ _, ?_⟩
      show Fin.tail (word x (-1) (n + 1)) = word x 0 n
      rw [tail_word, neg_add_cancel]
  exact (Set.ncard_image_iff (Set.toFinite _)).1 (by rw [himg, heq])

/-- **A subshift with boundedly many words of each length is finite** (tex 131–132). -/
theorem finite_of_ncard_language_le [Finite A] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) {C : ℕ} (hC : ∀ n, (language X n).ncard ≤ C) :
    X.Finite := by
  obtain ⟨n, hn1, heq⟩ : ∃ n : ℕ, 1 ≤ n ∧ (language X (n + 1)).ncard = (language X n).ncard := by
    by_contra h
    push Not at h
    have hgrow : ∀ n : ℕ, n ≤ (language X (n + 1)).ncard := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        have hlt : (language X (n + 1)).ncard < (language X (n + 1 + 1)).ncard :=
          lt_of_le_of_ne (ncard_language_le_succ X (n + 1)) (h (n + 1) (by omega)).symm
        omega
    have h1 := hC (C + 1 + 1)
    have h2 := hgrow (C + 1)
    omega
  have hinit := injOn_init_of_ncard_eq X heq
  have htail := injOn_tail_of_ncard_eq hX heq
  have hdet : ∀ x ∈ X, ∀ x' ∈ X, word x 0 n = word x' 0 n → ∀ i : ℤ, word x i n = word x' i n := by
    intro x hx x' hx' h0 i
    induction i with
    | zero => exact h0
    | succ i ih =>
      have hw : word x i (n + 1) = word x' i (n + 1) :=
        hinit (word_mem_language hX hx _ _) (word_mem_language hX hx' _ _)
          (by simp only [init_word]; exact ih)
      have hc := congrArg (fun w : Fin (n + 1) → A => Fin.tail w) hw
      simpa only [tail_word] using hc
    | pred i ih =>
      have hw : word x (-(i : ℤ) - 1) (n + 1) = word x' (-(i : ℤ) - 1) (n + 1) :=
        htail (word_mem_language hX hx _ _) (word_mem_language hX hx' _ _)
          (by simp only [tail_word, sub_add_cancel]; exact ih)
      have hc := congrArg (fun w : Fin (n + 1) → A => Fin.init w) hw
      simpa only [init_word] using hc
  refine Set.Finite.of_finite_image (f := fun x : ℤ → A => word x 0 n) (Set.toFinite _) ?_
  intro x hx x' hx' h
  funext j
  have hj := congrFun (hdet x hx x' hx' h j) ⟨0, hn1⟩
  simpa only [word_apply, Nat.cast_zero, add_zero] using hj

/-- **The number of words tends to infinity** for an infinite subshift (tex 131–132). -/
theorem tendsto_ncard_language [Finite A] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) (hinf : X.Infinite) :
    Tendsto (fun n => (language X n).ncard) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun C => ?_
  by_contra h
  push Not at h
  exact hinf (finite_of_ncard_language_le hX fun n => by
    obtain ⟨a, hna, ha⟩ := h n
    exact (ncard_language_mono X hna).trans ha.le)

/-! ### The periodic sequence `y` -/

variable {x : ℤ → A} {k m : ℕ}

/-- The `m`-periodic sequence that agrees with `x` on `[0, m)` (tex 124–125). -/
def periodicExt (x : ℤ → A) (m : ℕ) (t : ℤ) : A :=
  periodicWord x m (t : ZMod m)

theorem periodicExt_add_mul (x : ℤ → A) (m : ℕ) (t q : ℤ) :
    periodicExt x m (t + m * q) = periodicExt x m t := by
  simp only [periodicExt, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero]

/-- **`y` agrees with `x` on `[0, m + 2ℓ)`** (tex 124–126), since `x_{[m, m+2ℓ)} = x_{[0,2ℓ)}`. -/
theorem periodicExt_eq_of_lt [NeZero m] (hrep : word x 0 (2 * k) = word x m (2 * k))
    (hmk : 2 * k + 1 ≤ m) {t : ℕ} (ht : t < m + 2 * k) : periodicExt x m t = x t := by
  have h := periodicWord_natCast_eq hrep hmk ht
  simpa only [periodicExt, Int.cast_natCast] using h

/-- **Every window of `y` is a translate, by a multiple of `m`, of a window starting in `[0, m)`**
(tex 126–127). -/
theorem word_periodicExt_emod (x : ℤ → A) (m : ℕ) (t : ℤ) (n : ℕ) :
    word (periodicExt x m) t n = word (periodicExt x m) (t % m) n := by
  funext j
  simp only [word_apply]
  have h := Int.emod_add_mul_ediv t (m : ℤ)
  rw [show t + ((j : ℕ) : ℤ) = t % m + ((j : ℕ) : ℤ) + m * (t / m) by linarith]
  exact periodicExt_add_mul x m _ _

/-- **`y` has the same words of length `2ℓ + 1` as `X`** (tex 127–129). -/
theorem language_periodicExt [NeZero m] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) (hx : x ∈ X)
    (hrep : word x 0 (2 * k) = word x m (2 * k)) (hmk : 2 * k + 1 ≤ m)
    (hseg : ∀ u ∈ language X (2 * k + 1), ∃ i : ℕ, i + (2 * k + 1) ≤ m ∧ word x i (2 * k + 1) = u) :
    {w | ∃ t : ℤ, word (periodicExt x m) t (2 * k + 1) = w} = language X (2 * k + 1) := by
  have hwin : ∀ t : ℤ, word (periodicExt x m) t (2 * k + 1) =
      fun j : Fin (2 * k + 1) => periodicWord x m ((t : ZMod m) + (j : ℕ)) := by
    intro t
    funext j
    simp only [word_apply, periodicExt, Int.cast_add, Int.cast_natCast]
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    rw [hwin]
    exact periodicWord_window_mem_language hX hx hrep hmk _
  · intro hw
    obtain ⟨n, hn⟩ := periodicWord_exists_window_eq hrep hmk hseg hw
    refine ⟨(n.val : ℤ), ?_⟩
    rw [hwin, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hn

/-! ### Least periods -/

theorem iterate_shift_one (p : ℕ) (y : ℤ → A) : (shift (1 : ℤ))^[p] y = shift (p : ℤ) y := by
  induction p with
  | zero => rw [Function.iterate_zero, id_eq, Nat.cast_zero, shift_zero]
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [shift_apply]
    congr 1
    push_cast
    ring

theorem isPeriodicPt_shift_iff (y : ℤ → A) (p : ℕ) :
    Function.IsPeriodicPt (shift (1 : ℤ)) p y ↔ ∀ t : ℤ, y (p + t) = y t := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, iterate_shift_one, funext_iff]
  simp only [shift_apply]

/-- **The least period** of a sequence: its minimal period under the shift (tex 129–130). -/
noncomputable def leastPeriod (y : ℤ → A) : ℕ :=
  Function.minimalPeriod (shift (1 : ℤ)) y

theorem periodic_add_mul {y : ℤ → A} {N : ℕ} (hper : ∀ t : ℤ, y (N + t) = y t) (t q : ℤ) :
    y (t + N * q) = y t := by
  induction q with
  | zero => rw [mul_zero, add_zero]
  | succ q ih =>
    rw [show t + (N : ℤ) * ((q : ℤ) + 1) = N + (t + N * q) by ring, hper, ih]
  | pred q ih =>
    rw [← ih, show t + (N : ℤ) * (-(q : ℤ)) = N + (t + N * (-(q : ℤ) - 1)) by ring, hper]

theorem periodicExt_isPeriodicPt (x : ℤ → A) (m : ℕ) :
    Function.IsPeriodicPt (shift (1 : ℤ)) m (periodicExt x m) := by
  rw [isPeriodicPt_shift_iff]
  intro t
  rw [add_comm, show t + (m : ℤ) = t + m * 1 by ring, periodicExt_add_mul]

theorem leastPeriod_periodicExt_pos [NeZero m] (x : ℤ → A) : 0 < leastPeriod (periodicExt x m) :=
  (periodicExt_isPeriodicPt x m).minimalPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne m))

theorem periodicExt_leastPeriod_add (x : ℤ → A) (m : ℕ) (t : ℤ) :
    periodicExt x m (leastPeriod (periodicExt x m) + t) = periodicExt x m t :=
  (isPeriodicPt_shift_iff _ _).1 (Function.isPeriodicPt_minimalPeriod _ _) t

/-- **The least period is at least the number of words** (tex 129–131). -/
theorem ncard_language_le_leastPeriod [Finite A] [NeZero m] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) (hx : x ∈ X)
    (hrep : word x 0 (2 * k) = word x m (2 * k)) (hmk : 2 * k + 1 ≤ m)
    (hseg : ∀ u ∈ language X (2 * k + 1), ∃ i : ℕ, i + (2 * k + 1) ≤ m ∧ word x i (2 * k + 1) = u) :
    (language X (2 * k + 1)).ncard ≤ leastPeriod (periodicExt x m) := by
  classical
  have hN : 0 < leastPeriod (periodicExt x m) := leastPeriod_periodicExt_pos x
  have hsub : language X (2 * k + 1) ⊆
      ((Finset.univ : Finset (Fin (leastPeriod (periodicExt x m)))).image
        fun t : Fin (leastPeriod (periodicExt x m)) =>
          word (periodicExt x m) ((t : ℕ) : ℤ) (2 * k + 1) : Set (Fin (2 * k + 1) → A)) := by
    intro w hw
    rw [← language_periodicExt hX hx hrep hmk hseg] at hw
    obtain ⟨t, rfl⟩ := hw
    have hmod := Int.emod_nonneg t
      (by exact_mod_cast hN.ne' : ((leastPeriod (periodicExt x m) : ℕ) : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos t
      (by exact_mod_cast hN : (0 : ℤ) < ((leastPeriod (periodicExt x m) : ℕ) : ℤ))
    refine Finset.mem_coe.2 (Finset.mem_image.2
      ⟨⟨(t % (leastPeriod (periodicExt x m) : ℤ)).toNat, by omega⟩, Finset.mem_univ _, ?_⟩)
    show word (periodicExt x m) (((t % (leastPeriod (periodicExt x m) : ℤ)).toNat : ℕ) : ℤ)
        (2 * k + 1) = word (periodicExt x m) t (2 * k + 1)
    rw [Int.toNat_of_nonneg hmod]
    funext j
    simp only [word_apply]
    have h := periodic_add_mul (periodicExt_leastPeriod_add x m)
      (t % (leastPeriod (periodicExt x m) : ℤ) + ((j : ℕ) : ℤ)) (t / (leastPeriod (periodicExt x m) : ℤ))
    rw [← h]
    congr 1
    have := Int.emod_add_mul_ediv t (leastPeriod (periodicExt x m) : ℤ)
    linarith
  calc (language X (2 * k + 1)).ncard
      ≤ (((Finset.univ : Finset (Fin (leastPeriod (periodicExt x m)))).image
          fun t : Fin (leastPeriod (periodicExt x m)) =>
            word (periodicExt x m) ((t : ℕ) : ℤ) (2 * k + 1) : Finset _) : Set _).ncard :=
        Set.ncard_le_ncard hsub
    _ = ((Finset.univ : Finset (Fin (leastPeriod (periodicExt x m)))).image
          fun t : Fin (leastPeriod (periodicExt x m)) =>
            word (periodicExt x m) ((t : ℕ) : ℤ) (2 * k + 1)).card :=
        Set.ncard_coe_finset _
    _ ≤ (Finset.univ : Finset (Fin (leastPeriod (periodicExt x m)))).card := Finset.card_image_le
    _ = leastPeriod (periodicExt x m) := by rw [Finset.card_univ, Fintype.card_fin]

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.finite_of_ncard_language_le
#audit_axioms GroupApproximation.SimpleKazhdanSofic.tendsto_ncard_language
#audit_axioms GroupApproximation.SimpleKazhdanSofic.periodicExt_eq_of_lt
#audit_axioms GroupApproximation.SimpleKazhdanSofic.word_periodicExt_emod
#audit_axioms GroupApproximation.SimpleKazhdanSofic.language_periodicExt
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ncard_language_le_leastPeriod
