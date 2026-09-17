import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Complement
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: the coordinate unit `Z = y t_0 + s t_1`

Khanh (arXiv:2609.08428), proof of Lemma `lem:word-multiplier`:

> If `y = a_ix` and `b = η_i^*`, then `by = 1`, and `R ⊕ ker b ⇄ R`,
> `(t,z) ↦ yt + z` and `u ↦ (bu, u - ybu)` are mutually inverse.

`exists_complement` packages `ker η^*` as the image of an isometry `s` (induction on `η`,
from `complement_cons_zero/one` and `complement_nil_zero/one`). `exists_coordinate_unit`
turns the displayed inverse pair into a unit `Z` of `A` with `Z s_0 = y`, whenever
`η^* y = 1` and `η ≠ []`.
-/

namespace GroupApproximation.Full.LVFrame


variable {A : Type*} [Ring A] (L : LeavittFamily A)

theorem complement_single (i : Fin 2) :
    ∃ s s' : A, L.wordT [i] * s = 0 ∧ s' * s = 1 ∧ s * s' + L.wordS [i] * L.wordT [i] = 1 := by
  revert i
  simp only [Fin.forall_fin_two]
  exact ⟨complement_nil_zero L, complement_nil_one L⟩

#audit_axioms GroupApproximation.Full.LVFrame.complement_single

theorem complement_cons (i : Fin 2) (a : List (Fin 2)) (r r' : A) (h1 : L.wordT a * r = 0)
    (h2 : r' * r = 1) (h3 : r * r' + L.wordS a * L.wordT a = 1) :
    ∃ s s' : A, L.wordT (i :: a) * s = 0 ∧ s' * s = 1 ∧
      s * s' + L.wordS (i :: a) * L.wordT (i :: a) = 1 := by
  revert i
  simp only [Fin.forall_fin_two]
  exact ⟨complement_cons_zero L a r r' h1 h2 h3, complement_cons_one L a r r' h1 h2 h3⟩

#audit_axioms GroupApproximation.Full.LVFrame.complement_cons

/-- Every nonempty word `η` has an isometric complement `s` of its cylinder:
`η^* s = 0`, `s' s = 1`, `s s' + η η^* = 1` (Khanh, eq. `sibling-kernel`). -/
theorem exists_complement (η : List (Fin 2)) (hη : η ≠ []) :
    ∃ s s' : A, L.wordT η * s = 0 ∧ s' * s = 1 ∧ s * s' + L.wordS η * L.wordT η = 1 := by
  induction η with
  | nil => exact absurd rfl hη
  | cons i a ih =>
      by_cases ha : a = []
      · subst ha
        exact complement_single L i
      · obtain ⟨r, r', h1, h2, h3⟩ := ih ha
        exact complement_cons L i a r r' h1 h2 h3

#audit_axioms GroupApproximation.Full.LVFrame.exists_complement

theorem coordinate_left_inv {b y s s' : A} (hby : b * y = 1) (hbs : b * s = 0)
    (hs : s' * s = 1) :
    (L.s0 * b + L.s1 * (s' * (1 - y * b))) * (y * L.t0 + s * L.t1) = 1 := by
  calc
    (L.s0 * b + L.s1 * (s' * (1 - y * b))) * (y * L.t0 + s * L.t1) =
        L.s0 * (b * y) * L.t0 + L.s0 * (b * s) * L.t1 + L.s1 * s' * (y - y * (b * y)) * L.t0 +
          L.s1 * (s' * s) * L.t1 - L.s1 * s' * y * (b * s) * L.t1 := by
      noncomm_ring
    _ = L.s0 * L.t0 + L.s1 * L.t1 := by
      rw [hby, hbs, hs]
      noncomm_ring
    _ = 1 := L.sum_range

#audit_axioms GroupApproximation.Full.LVFrame.coordinate_left_inv

theorem coordinate_right_inv {b y s s' S : A} (hby : b * y = 1) (hsS : s * s' + S * b = 1) :
    (y * L.t0 + s * L.t1) * (L.s0 * b + L.s1 * (s' * (1 - y * b))) = 1 := by
  have hss : s * s' = 1 - S * b := eq_sub_of_add_eq hsS
  calc
    (y * L.t0 + s * L.t1) * (L.s0 * b + L.s1 * (s' * (1 - y * b))) =
        y * (L.t0 * L.s0) * b + y * (L.t0 * L.s1) * (s' * (1 - y * b)) +
          s * (L.t1 * L.s0) * b + s * (L.t1 * L.s1) * (s' * (1 - y * b)) := by
      noncomm_ring
    _ = y * b + s * s' - s * s' * y * b := by
      rw [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]
      noncomm_ring
    _ = y * b + (1 - S * b) - (1 - S * b) * y * b := by
      rw [hss]
    _ = 1 - S * b + S * (b * y) * b := by
      noncomm_ring
    _ = 1 := by
      rw [hby]
      noncomm_ring

#audit_axioms GroupApproximation.Full.LVFrame.coordinate_right_inv

/-- **Coordinate unit.** If `η ≠ []` and `η^* y = 1`, there is a unit `Z` with `Z s_0 = y`. -/
theorem exists_coordinate_unit (η : List (Fin 2)) (hη : η ≠ []) {y : A}
    (hy : L.wordT η * y = 1) : ∃ Z : Aˣ, (Z : A) * L.s0 = y := by
  obtain ⟨s, s', hbs, hs, hsS⟩ := exists_complement L η hη
  refine ⟨⟨y * L.t0 + s * L.t1, L.s0 * L.wordT η + L.s1 * (s' * (1 - y * L.wordT η)),
    coordinate_right_inv L hy hsS, coordinate_left_inv L hy hbs hs⟩, ?_⟩
  change (y * L.t0 + s * L.t1) * L.s0 = y
  calc
    (y * L.t0 + s * L.t1) * L.s0 = y * (L.t0 * L.s0) + s * (L.t1 * L.s0) := by noncomm_ring
    _ = y := by
      rw [L.t0_s0, L.t1_s0]
      noncomm_ring

#audit_axioms GroupApproximation.Full.LVFrame.exists_coordinate_unit

end GroupApproximation.Full.LVFrame
