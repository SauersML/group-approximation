import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsForwardOrbit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsLeastPeriod
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, proof of `thm:main`: the periodic words, with centered windows

`simple_kazhdan_sofic_group.tex` at f34e9c0b1, "Proof of Theorem~\ref{thm:main}":

> Fix $x\in X$ and $\ell\ge0$. By minimality the forward orbit of $x$ is dense, so every word of $X$
> occurs in $x_{[0,\infty)}$, and $x_{[-\ell,\ell]}$ recurs at arbitrarily large positions. So there is
> $m$ with $x_{[m-\ell,m+\ell]}=x_{[-\ell,\ell]}$ such that every word of length $2\ell+1$ of $X$ occurs
> in $x_{[0,m)}$. The $m$-periodic sequence $y_\ell$ that agrees with $x$ on $[0,m)$ then agrees with
> $x$ on $[-\ell,m+\ell]$. Every window of length $2\ell+1$ of $y_\ell$ is a translate of one centered
> in $[0,m)$, so $y_\ell$ has the same words of length $2\ell+1$ as $X$.

The landed carriers of ms-units read the recurrence of the uncentered word `x_{[0,2ℓ)}`.  This module
proves the printed centered statements:

* `exists_centered_recurrence`: `x_{[-ℓ,ℓ]}` recurs at arbitrarily large positions `m`;
* `exists_centered_occurrences`: one such `m ≥ 2ℓ + 1` with every word of length `2ℓ + 1` inside
  `x_{[0,m)}`;
* `periodicExt_eq_of_centered`: the `m`-periodic `y_ℓ` agrees with `x` on `[-ℓ, m + ℓ]`;
* `word_periodicExt_center_emod`, `language_periodicExt_centered`: every window is a translate of one
  centered in `[0, m)`, and `y_ℓ` has the same words of length `2ℓ + 1` as `X`;
* closed endpoints `printedCenteredRecurrence`, `printedCenteredOccurrences`,
  `printedPeriodicAgreesCentered`, `printedCenteredWindowsSameWords`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift WordGraph

section Centered

variable {A : Type*}

/-- tex 247–248: "$x_{[-\ell,\ell]}$ recurs at arbitrarily large positions". -/
theorem exists_centered_recurrence [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ m : ℤ, Set.MapsTo (shift m) X X)
    (hmin : ∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) →
      C = ∅ ∨ C = X) {x : ℤ → A} (hx : x ∈ X) (ℓ M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1) := by
  have hu : word x (-(ℓ : ℤ)) (2 * ℓ + 1) ∈ language X (2 * ℓ + 1) := word_mem_language hX hx _ _
  obtain ⟨i, hi⟩ := exists_nat_word_eq_of_minimal hXc hX hmin (hX (M : ℤ) hx) hu
  rw [word_shift] at hi
  refine ⟨M + i + ℓ, by omega, ?_⟩
  rw [show ((M + i + ℓ : ℕ) : ℤ) - ℓ = (M : ℤ) + (i : ℤ) by push_cast; ring]
  exact hi

/-- tex 248–250: "So there is $m$ with $x_{[m-\ell,m+\ell]}=x_{[-\ell,\ell]}$ such that every word of
length $2\ell+1$ of $X$ occurs in $x_{[0,m)}$", with `m ≥ max M (2ℓ + 1)`. -/
theorem exists_centered_occurrences [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ m : ℤ, Set.MapsTo (shift m) X X)
    (hmin : ∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) →
      C = ∅ ∨ C = X) {x : ℤ → A} (hx : x ∈ X) (ℓ M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ 2 * ℓ + 1 ≤ m ∧
      word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1) ∧
      ∀ u ∈ language X (2 * ℓ + 1), ∃ i : ℕ, i + (2 * ℓ + 1) ≤ m ∧ word x i (2 * ℓ + 1) = u := by
  classical
  have hfin : (language X (2 * ℓ + 1)).Finite := Set.toFinite _
  haveI : Fintype ↥(language X (2 * ℓ + 1)) := hfin.fintype
  choose pos hpos using fun u : ↥(language X (2 * ℓ + 1)) =>
    exists_nat_word_eq_of_minimal hXc hX hmin hx u.2
  set B : ℕ := (Finset.univ : Finset ↥(language X (2 * ℓ + 1))).sup fun u => pos u + (2 * ℓ + 1)
  obtain ⟨m, hm, hrec⟩ := exists_centered_recurrence hXc hX hmin hx ℓ (max M (B + 2 * ℓ + 1))
  have h1 := le_max_left M (B + 2 * ℓ + 1)
  have h2 := le_max_right M (B + 2 * ℓ + 1)
  refine ⟨m, by omega, by omega, hrec, fun u hu => ⟨pos ⟨u, hu⟩, ?_, hpos ⟨u, hu⟩⟩⟩
  have h3 := Finset.le_sup (f := fun u : ↥(language X (2 * ℓ + 1)) => pos u + (2 * ℓ + 1))
    (Finset.mem_univ ⟨u, hu⟩)
  omega

variable {x : ℤ → A} {m ℓ : ℕ}

/-- The `m`-periodic sequence reads `x` at the residue: `y_ℓ(t) = x(t mod m)`. -/
theorem periodicExt_eq_emod [NeZero m] (x : ℤ → A) (t : ℤ) : periodicExt x m t = x (t % m) := by
  show x (((t : ZMod m).val : ℕ) : ℤ) = x (t % m)
  rw [ZMod.val_intCast]

/-- tex 250–251: "The $m$-periodic sequence $y_\ell$ that agrees with $x$ on $[0,m)$ then agrees with
$x$ on $[-\ell,m+\ell]$". -/
theorem periodicExt_eq_of_centered [NeZero m] (hml : 2 * ℓ + 1 ≤ m)
    (hrec : word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1)) {t : ℤ}
    (ht1 : -(ℓ : ℤ) ≤ t) (ht2 : t ≤ m + ℓ) : periodicExt x m t = x t := by
  rw [periodicExt_eq_emod]
  have hrec' : ∀ j : ℕ, j < 2 * ℓ + 1 → x ((m : ℤ) - ℓ + j) = x (-(ℓ : ℤ) + j) := by
    intro j hj
    have h := congrFun hrec ⟨j, hj⟩
    simpa only [word_apply] using h
  rcases lt_or_ge t 0 with hneg | hnn
  · have hmod : t % (m : ℤ) = t + m := by
      have h1 := Int.add_mul_emod_self_left t (m : ℤ) 1
      rw [mul_one] at h1
      rw [← h1]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t + ℓ := ⟨(t + ℓ).toNat, Int.toNat_of_nonneg (by omega)⟩
    have h := hrec' j (by omega)
    rw [show (m : ℤ) - ℓ + j = t + m by omega, show -(ℓ : ℤ) + j = t by omega] at h
    exact h
  · rcases lt_or_ge t m with hlt | hge
    · rw [Int.emod_eq_of_lt hnn hlt]
    · have hmod : t % (m : ℤ) = t - m := by
        have h1 := Int.add_mul_emod_self_left (t - m) (m : ℤ) 1
        rw [mul_one, sub_add_cancel] at h1
        rw [h1]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hmod]
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t - m + ℓ := ⟨(t - m + ℓ).toNat, Int.toNat_of_nonneg (by omega)⟩
      have h := hrec' j (by omega)
      rw [show (m : ℤ) - ℓ + j = t by omega, show -(ℓ : ℤ) + j = t - m by omega] at h
      exact h.symm

/-- tex 252–253: "Every window of length $2\ell+1$ of $y_\ell$ is a translate of one centered in
$[0,m)$": the window centered at `t` equals the window centered at `t mod m`. -/
theorem word_periodicExt_center_emod [NeZero m] (x : ℤ → A) (t : ℤ) :
    word (periodicExt x m) (t - ℓ) (2 * ℓ + 1) = word (periodicExt x m) (t % m - ℓ) (2 * ℓ + 1) := by
  funext j
  simp only [word_apply]
  have h := Int.emod_add_mul_ediv t (m : ℤ)
  rw [show t - ℓ + ((j : ℕ) : ℤ) = t % m - ℓ + ((j : ℕ) : ℤ) + m * (t / m) by linarith]
  exact periodicExt_add_mul x m _ _

/-- tex 252–254: "so $y_\ell$ has the same words of length $2\ell+1$ as $X$". -/
theorem language_periodicExt_centered [NeZero m] {X : Set (ℤ → A)}
    (hX : ∀ g : ℤ, Set.MapsTo (shift g) X X) (hx : x ∈ X) (hml : 2 * ℓ + 1 ≤ m)
    (hrec : word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1))
    (hseg : ∀ u ∈ language X (2 * ℓ + 1), ∃ i : ℕ, i + (2 * ℓ + 1) ≤ m ∧ word x i (2 * ℓ + 1) = u) :
    {w | ∃ t : ℤ, word (periodicExt x m) t (2 * ℓ + 1) = w} = language X (2 * ℓ + 1) := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    have hs : word (periodicExt x m) s (2 * ℓ + 1) =
        word (periodicExt x m) ((s + ℓ) % m - ℓ) (2 * ℓ + 1) := by
      rw [← word_periodicExt_center_emod x (s + ℓ), add_sub_cancel_right]
    rw [hs]
    have hc1 := Int.emod_nonneg (s + ℓ) hm0.ne'
    have hc2 := Int.emod_lt_of_pos (s + ℓ) hm0
    have heq : word (periodicExt x m) ((s + ℓ) % m - ℓ) (2 * ℓ + 1) =
        word x ((s + ℓ) % m - ℓ) (2 * ℓ + 1) := by
      funext j
      simp only [word_apply]
      exact periodicExt_eq_of_centered hml hrec (by omega) (by have := j.2; omega)
    rw [heq]
    exact word_mem_language hX hx _ _
  · intro hw
    obtain ⟨i, hi, rfl⟩ := hseg w hw
    refine ⟨i, ?_⟩
    funext j
    simp only [word_apply]
    exact periodicExt_eq_of_centered hml hrec (by omega) (by have := j.2; omega)

end Centered

/-- **tex 246–248**, closed: in a minimal subshift over a finite alphabet the forward orbit of `x` is
dense, every word of `X` occurs in `x_{[0,∞)}`, and `x_{[-ℓ,ℓ]}` recurs at arbitrarily large
positions. -/
def PrintedCenteredRecurrence : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (X : Set (ℤ → A)),
    IsClosed X → (∀ m : ℤ, Set.MapsTo (shift m) X X) →
    (∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) → C = ∅ ∨ C = X) →
    ∀ x ∈ X, X ⊆ closure (Set.range fun n : ℕ => shift (n : ℤ) x) ∧
      (∀ (n : ℕ) (u : Fin n → A), u ∈ language X n → ∃ i : ℕ, word x i n = u) ∧
      ∀ ℓ M : ℕ, ∃ m : ℕ, M ≤ m ∧ word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1)

theorem printedCenteredRecurrence : PrintedCenteredRecurrence := by
  intro A _ _ _ X hXc hX hmin x hx
  exact ⟨subset_closure_forwardOrbit_of_minimal hXc hX hmin hx,
    fun _ _ hu => exists_nat_word_eq_of_minimal hXc hX hmin hx hu,
    exists_centered_recurrence hXc hX hmin hx⟩

/-- **tex 248–250**, closed. -/
def PrintedCenteredOccurrences : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (X : Set (ℤ → A)),
    IsClosed X → (∀ m : ℤ, Set.MapsTo (shift m) X X) →
    (∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) → C = ∅ ∨ C = X) →
    ∀ x ∈ X, ∀ ℓ : ℕ, ∃ m : ℕ, 2 * ℓ + 1 ≤ m ∧
      word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1) ∧
      ∀ u ∈ language X (2 * ℓ + 1), ∃ i : ℕ, i + (2 * ℓ + 1) ≤ m ∧ word x i (2 * ℓ + 1) = u

theorem printedCenteredOccurrences : PrintedCenteredOccurrences := by
  intro A _ _ _ X hXc hX hmin x hx ℓ
  obtain ⟨m, -, hm, hrec, hseg⟩ := exists_centered_occurrences hXc hX hmin hx ℓ 0
  exact ⟨m, hm, hrec, hseg⟩

/-- **tex 250–251**, closed. -/
def PrintedPeriodicAgreesCentered : Prop :=
  ∀ (A : Type) (x : ℤ → A) (m ℓ : ℕ) [NeZero m], 2 * ℓ + 1 ≤ m →
    word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1) →
    ∀ t : ℤ, -(ℓ : ℤ) ≤ t → t ≤ m + ℓ → periodicExt x m t = x t

theorem printedPeriodicAgreesCentered : PrintedPeriodicAgreesCentered :=
  fun _ _ _ _ _ hml hrec _ ht1 ht2 => periodicExt_eq_of_centered hml hrec ht1 ht2

/-- **tex 252–254**, closed. -/
def PrintedCenteredWindowsSameWords : Prop :=
  ∀ (A : Type) (X : Set (ℤ → A)) (x : ℤ → A) (m ℓ : ℕ) [NeZero m],
    (∀ g : ℤ, Set.MapsTo (shift g) X X) → x ∈ X → 2 * ℓ + 1 ≤ m →
    word x ((m : ℤ) - ℓ) (2 * ℓ + 1) = word x (-(ℓ : ℤ)) (2 * ℓ + 1) →
    (∀ u ∈ language X (2 * ℓ + 1), ∃ i : ℕ, i + (2 * ℓ + 1) ≤ m ∧ word x i (2 * ℓ + 1) = u) →
    (∀ t : ℤ, word (periodicExt x m) (t - ℓ) (2 * ℓ + 1) =
      word (periodicExt x m) (t % m - ℓ) (2 * ℓ + 1)) ∧
    {w | ∃ t : ℤ, word (periodicExt x m) t (2 * ℓ + 1) = w} = language X (2 * ℓ + 1)

theorem printedCenteredWindowsSameWords : PrintedCenteredWindowsSameWords :=
  fun _ _ x _ _ _ hX hx hml hrec hseg =>
    ⟨word_periodicExt_center_emod x, language_periodicExt_centered hX hx hml hrec hseg⟩

end SimpleKazhdanSofic

end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedCenteredRecurrence
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedCenteredOccurrences
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedPeriodicAgreesCentered
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedCenteredWindowsSameWords
