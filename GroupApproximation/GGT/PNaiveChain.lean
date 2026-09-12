import GroupApproximation.GGT.PNaiveTransversal

/-!
# The orbit chain of a local gap, fellow travelling, and finite exceptional sets

Fourth module of property `P_naive` (Abbott--Dahmani, arXiv:1610.04143).  The
ping-pong of `GGT/PNaivePingPong.lean` needs one transversality constant for
*every* nontrivial element of a cyclic subgroup `⟨f⟩`.  When `f` moves the
basepoint boundedly and has infinite order there are infinitely many such
elements, and the constant comes from acylindricity.  This module supplies the
geometry that acylindricity is applied to.

Throughout, `h` has a strong local gap at `o`: its turn `(h·o | h⁻¹·o)_o` is at
most `C`, and its step `d(o, h·o)` exceeds `2(C + 2δ)`.  Write `pᵢ = hⁱ·o` and
`qᵢ = h⁻ⁱ·o`.

* `gromovProduct_inv_pow_pow_le` — the two halves of the orbit meet at the
  basepoint with turn at most `C + 2δ`: `(qᵢ | pⱼ)_o ≤ C + 2δ` for `i, j ≥ 1`;
* `gromovProduct_turn_pow_le` — so every power `hᴹ` has turn at most `C + 2δ`,
  and `le_dist_pow_smul` — its step grows linearly;
* `le_gromovProduct_pow_pow` — an earlier vertex lies between the basepoint and
  a later one: `d(o, pᵢ) − (C + 2δ) ≤ (pᵢ | pⱼ)_o` for `1 ≤ i < j`;
* `dist_smul_le_of_fellow` — **fellow travelling**: if `g` moves `o` by at most
  `E` and some translate `g·pₙ` follows some chain vertex `c` from `o` at least
  as long as the depth `r` of two vertices `a, b` of the two chains, then
  `d(b, g·a) ≤ 2C + 8δ + 3E`;
* `finite_of_translate_mem` — a set all of whose left quotients by one of its
  members lie in a finite set is finite.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- A Gromov product based at one of its endpoints vanishes. -/
theorem gromovProduct_self_base (o z : X) : gromovProduct o z o = 0 := by
  unfold gromovProduct
  rw [dist_self, dist_comm z o]
  ring

/-! ## The two halves of the orbit -/

/-- **Positive powers stay transverse to `h⁻¹·o`, and deep toward `h·o`.** -/
theorem gromovProduct_pow_orbit {δ C : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) (n : ℕ) (hn : 1 ≤ n) :
    dist o (h • o) - (C + δ) ≤ gromovProduct ((h ^ n) • o) (h • o) o ∧
      gromovProduct ((h ^ n) • o) (h⁻¹ • o) o ≤ C + δ := by
  have hgap' : 2 * (C + δ) < dist o (h • o) := by linarith
  have hx : gromovProduct o (h⁻¹ • o) o ≤ C + δ := by
    rw [gromovProduct_self_base]
    linarith
  exact gromovProduct_pow_smul hδ hiso hloc hgap' hx n hn

/-- **The same for the negative powers.** -/
theorem gromovProduct_inv_pow_orbit {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) (n : ℕ) (hn : 1 ≤ n) :
    dist o (h • o) - (C + δ) ≤ gromovProduct ((h⁻¹ ^ n) • o) (h⁻¹ • o) o ∧
      gromovProduct ((h⁻¹ ^ n) • o) (h • o) o ≤ C + δ := by
  have hloc' : gromovProduct (h⁻¹ • o) (h⁻¹⁻¹ • o) o ≤ C := by
    rw [gromovProduct_inv_turn]
    exact hloc
  have hgap' : 2 * (C + 2 * δ) < dist o (h⁻¹ • o) := by
    rw [dist_inv_smul hiso]
    exact hgap
  have key := gromovProduct_pow_orbit hδ hδ0 hiso hloc' hC hgap' n hn
  rw [dist_inv_smul hiso, inv_inv] at key
  exact key

/-- **The two halves meet at the basepoint with a bounded turn.** -/
theorem gromovProduct_inv_pow_pow_le {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    gromovProduct ((h⁻¹ ^ i) • o) ((h ^ j) • o) o ≤ C + 2 * δ := by
  have hneg := (gromovProduct_inv_pow_orbit hδ hδ0 hiso hloc hC hgap i hi).1
  have hpos := (gromovProduct_pow_orbit hδ hδ0 hiso hloc hC hgap j hj).2
  have hfar : gromovProduct (h⁻¹ • o) ((h ^ j) • o) o + δ <
      gromovProduct ((h⁻¹ ^ i) • o) (h⁻¹ • o) o := by
    rw [gromovProduct_comm (h⁻¹ • o)]
    linarith
  have hup := gromovProduct_le_add_delta_of_lt hδ hfar
  rw [gromovProduct_comm (h⁻¹ • o)] at hup
  linarith

/-- **Every positive power has turn at most `C + 2δ`.** -/
theorem gromovProduct_turn_pow_le {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) {M : ℕ} (hM : 1 ≤ M) :
    gromovProduct ((h ^ M) • o) ((h ^ M)⁻¹ • o) o ≤ C + 2 * δ := by
  have key := gromovProduct_inv_pow_pow_le hδ hδ0 hiso hloc hC hgap hM hM
  rw [inv_pow, gromovProduct_comm] at key
  exact key

/-- **The step of a power grows linearly.** -/
theorem le_dist_pow_smul {δ C : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) (M : ℕ) :
    (dist o (h • o) - 2 * (C + δ)) * M ≤ dist o ((h ^ M) • o) := by
  let y : ℕ → X := fun n => (h ^ n) • o
  have hedge : ∀ n : ℕ, dist o (h • o) ≤ dist (y n) (y (n + 1)) := by
    intro n
    have hmove := hiso (h ^ n) o (h • o)
    rw [smul_smul, ← pow_succ] at hmove
    exact le_of_eq hmove.symm
  have hlocal : ∀ n : ℕ, gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ C := by
    intro n
    have hsm := gromovProduct_smul hiso (h ^ n) o ((h ^ 2) • o) (h • o)
    rw [smul_smul, ← pow_add, smul_smul, ← pow_succ] at hsm
    change gromovProduct (y n) (y (n + 2)) (y (n + 1)) =
      gromovProduct o ((h ^ 2) • o) (h • o) at hsm
    rw [hsm, ← gromovProduct_turn_eq hiso]
    exact hloc
  have hCδ : 0 ≤ C + δ := by linarith
  have hgap' : 2 * (C + δ) < dist o (h • o) := by linarith
  have hall := chain_backtracking_and_progress hδ hCδ hgap' y hedge hlocal M
  simpa [y] using hall.1

/-! ## Vertices between the basepoint and later vertices -/

/-- **An earlier vertex lies between the basepoint and a later vertex.** -/
theorem le_gromovProduct_pow_pow {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o)) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    dist o ((h ^ i) • o) - (C + 2 * δ) ≤
      gromovProduct ((h ^ i) • o) ((h ^ j) • o) o := by
  have htrans : gromovProduct o ((h ^ j) • o) ((h ^ i) • o) =
      gromovProduct ((h⁻¹ ^ i) • o) ((h ^ (j - i)) • o) o := by
    have e1 : (h ^ i) • (h⁻¹ ^ i) • o = o := by
      rw [smul_smul, inv_pow, mul_inv_cancel, one_smul]
    have e2 : (h ^ i) • (h ^ (j - i)) • o = (h ^ j) • o := by
      rw [smul_smul, ← pow_add, Nat.add_sub_of_le hij.le]
    have hsm := gromovProduct_smul hiso (h ^ i) ((h⁻¹ ^ i) • o) ((h ^ (j - i)) • o) o
    rw [e1, e2] at hsm
    exact hsm
  have hbetween :=
    gromovProduct_inv_pow_pow_le hδ hδ0 hiso hloc hC hgap hi (by omega : 1 ≤ j - i)
  have hswap := gromovProduct_add_swap_base ((h ^ j) • o) ((h ^ i) • o) o
  rw [gromovProduct_comm ((h ^ j) • o) o, htrans] at hswap
  rw [gromovProduct_comm ((h ^ i) • o), dist_comm]
  linarith

/-! ## Fellow travelling -/

/-- **Fellow travelling.**  Let `g` move `o` by at most `E`.  Suppose `a` and `b`
are at the same distance `r` from `o`, that `a` lies between `o` and `a'`, that
`b` lies between `o` and `c` (both with defect `C + 2δ`), and that the translate
`g·a'` follows `c` from `o` for at least `r`.  Then `d(b, g·a) ≤ 2C + 8δ + 3E`. -/
theorem dist_smul_le_of_fellow {δ C E r : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {g : G} {o a a' b c : X}
    (hE : dist o (g • o) ≤ E) (hra : dist o a = r) (hrb : dist o b = r)
    (hb : r - (C + 2 * δ) ≤ gromovProduct b c o)
    (ha : r - (C + 2 * δ) ≤ gromovProduct a a' o)
    (hT : r ≤ gromovProduct (g • a') c o) (hCδ : 0 ≤ C + 2 * δ) (hδ0 : 0 ≤ δ) :
    dist b (g • a) ≤ 2 * C + 8 * δ + 3 * E := by
  have hE0 : 0 ≤ E := le_trans dist_nonneg hE
  -- the translated between-ness, at the moved basepoint and then at `o`
  have hsm : gromovProduct (g • a) (g • a') (g • o) = gromovProduct a a' o :=
    gromovProduct_smul hiso g a a' o
  have hbase := gromovProduct_le_add_dist_base (g • a) (g • a') (g • o) o
  have hdgo : dist (g • o) o ≤ E := by
    rw [dist_comm]
    exact hE
  have hga : r - (C + 2 * δ) - E ≤ gromovProduct (g • a') (g • a) o := by
    rw [gromovProduct_comm]
    linarith
  -- four-point, twice
  have h4a := hδ o b c (g • a')
  have hmin1 : r - (C + 2 * δ) ≤ min (gromovProduct b c o) (gromovProduct c (g • a') o) := by
    refine le_min hb ?_
    rw [gromovProduct_comm]
    linarith
  have hbga' : r - (C + 2 * δ) - δ ≤ gromovProduct b (g • a') o := by linarith
  have h4b := hδ o b (g • a') (g • a)
  have hmin2 : r - (C + 2 * δ) - δ - E ≤
      min (gromovProduct b (g • a') o) (gromovProduct (g • a') (g • a) o) :=
    le_min (by linarith) (by linarith)
  have hbga : r - (C + 2 * δ) - 2 * δ - E ≤ gromovProduct b (g • a) o := by linarith
  -- distances
  have hdga : dist (g • a) o ≤ r + E := by
    have htri := dist_triangle (g • a) (g • o) o
    rw [hiso g a o, dist_comm a o, hra] at htri
    linarith
  have hdb : dist b o = r := by
    rw [dist_comm]
    exact hrb
  unfold gromovProduct at hbga
  rw [hdb] at hbga
  linarith

/-! ## Finite exceptional sets -/

/-- **A set whose left quotients by one member lie in a finite set is finite.** -/
theorem finite_of_translate_mem {T S : Set G} (hS : S.Finite) {g₁ : G}
    (hmem : ∀ g ∈ T, g₁⁻¹ * g ∈ S) : T.Finite := by
  refine (hS.image fun s => g₁ * s).subset ?_
  intro g hg
  exact ⟨g₁⁻¹ * g, hmem g hg, by simp⟩

/-- **Elements that carry `p` near `q` and move `o` little form a finite set**,
when acylindricity bounds the elements moving `o` and `p` little. -/
theorem finite_of_carry {E ε : ℝ} (hiso : IsIsometricAction G X) {o p q : X}
    (hfin : {s : G | dist o (s • o) ≤ 2 * max E ε ∧ dist p (s • p) ≤ 2 * max E ε}.Finite) :
    {g : G | dist o (g • o) ≤ E ∧ dist q (g • p) ≤ ε}.Finite := by
  by_cases hne : {g : G | dist o (g • o) ≤ E ∧ dist q (g • p) ≤ ε}.Nonempty
  · obtain ⟨g₁, hg₁o, hg₁p⟩ := hne
    refine finite_of_translate_mem hfin (g₁ := g₁) ?_
    rintro g ⟨hgo, hgp⟩
    constructor
    · have hmove : dist o ((g₁⁻¹ * g) • o) = dist (g₁ • o) (g • o) := by
        have := hiso g₁ o ((g₁⁻¹ * g) • o)
        rw [smul_smul, mul_inv_cancel_left] at this
        exact this.symm
      rw [hmove]
      have htri := dist_triangle (g₁ • o) o (g • o)
      rw [dist_comm (g₁ • o) o] at htri
      have h1 : E ≤ max E ε := le_max_left E ε
      linarith
    · have hmove : dist p ((g₁⁻¹ * g) • p) = dist (g₁ • p) (g • p) := by
        have := hiso g₁ p ((g₁⁻¹ * g) • p)
        rw [smul_smul, mul_inv_cancel_left] at this
        exact this.symm
      rw [hmove]
      have htri := dist_triangle (g₁ • p) q (g • p)
      rw [dist_comm (g₁ • p) q] at htri
      have h1 : ε ≤ max E ε := le_max_right E ε
      linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_inv_pow_pow_le
#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_turn_pow_le
#audit_axioms GroupApproximation.GGT.PNaive.le_dist_pow_smul
#audit_axioms GroupApproximation.GGT.PNaive.le_gromovProduct_pow_pow
#audit_axioms GroupApproximation.GGT.PNaive.dist_smul_le_of_fellow
#audit_axioms GroupApproximation.GGT.PNaive.finite_of_carry
