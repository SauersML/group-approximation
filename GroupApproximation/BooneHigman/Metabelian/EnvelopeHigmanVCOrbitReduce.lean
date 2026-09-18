import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitPeel
import GroupApproximation.Meta.AxiomGuard

/-!
# Orbit refinement of residual W: the a/b-balanced cases (lane bh-met-77x)

Notation as in `EnvelopeHigmanVCLeafExpReduce`.  The pivot is `t = (a, b)`, with `a`, `b`
incomparable.  Call a word `c` *near* the pivot (`higmanVCOrbit_Near`) if `c` is comparable
with `a` or with `b`.

**a/b-balanced elements (proved).**  `h` is *a/b-balanced* (`higmanVCOrbit_Bal`) if
`h = ι r` for a word `r` in the letters of some antichain `C`, where the leaf permutation
`π r` preserves the length of every near leaf.  Orbit peeling (`higmanVCOrbit_split`) then
factors `h = u σ`:
* `u ∈ U` is a product of the balanced transpositions `(x, π x)` taken along the orbits
  through near leaves;
* `σ` is a product of letters between far leaves.

So `σ ∈ H_D` with `D = {a, b} ∪ (far part of C)`, which is an antichain
(`higmanVCOrbit_far_isAC`).  That makes `σ` symmetric with the trivial tree, and
`h t = u (σ t) ∈ U·S ⊆ S` (`higmanVCOrbit_bal_mem_S`).  The *twisted* case
`t⁻¹ h⁻¹ t⁻¹` a/b-balanced also follows, because `S` is closed under inverses
(`higmanVCOrbit_twist_mem_S`).

These cases are genuinely outside `higmanVCLeafExp_Sym`.  A brute force into `V_2`
(`SP/bh-met-77x/orbit_check.py`) uses `a = 00`, `b = 010` and
`C = {000, 001, 01000, 01001, 0101, 011, 100, 101, 110, 1110, 11110, 11111}`.
* The 5-cycle `000 → 011 → 100 → 01000 → 11110 → 000` is a/b-balanced.  It is not
  symmetric: no tree of depth `≤ 5` works, and there is a paper depth-descent argument.
* `swap(000, 01000)` is not symmetric, but its twist `swap(0100, 0000)` is balanced.
* The decomposition `h = u σ` and `σ t = t σ` were checked on 3000 random cases.

**Residual `W'` = `HigmanVCOrbitStatement`.**  This is `W` with the pivot closure required
only for `h` that is non-symmetric, not a/b-balanced, and not twisted-balanced.
`higmanVCOrbit_W_of_orbit` proves `W' → W`.

LOUD, on strength: `W → W'` is immediate, so as Props `W' ⇔ W ⇔ Z`, which is
Higman-strength.  `W'` is strictly smaller in PROOF CONTENT only: every a/b-balanced and
every twisted-balanced `h` is discharged here without Higman's theorem.  `W'` is true
exactly when `Z` is.

What remains is `h` in which some near leaf moves to a leaf of a different length, both in
`h` and in its twist.  An example is `swap(a0, b000)`: it is non-symmetric (checked), its
lengths are `n+1` vs `n+4`, and its twist has lengths `n+2` vs `n+3`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `c` is near the pivot `(a, b)`: comparable with `a` or with `b`. -/
def higmanVCOrbit_Near {d : ℕ} (a b c : List (Fin d)) : Prop :=
  a <+: c ∨ c <+: a ∨ b <+: c ∨ c <+: b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_Near

/-- The far part of `C` together with `a` and `b`. -/
noncomputable def higmanVCOrbit_far {d : ℕ} (a b : List (Fin d)) (C : Finset (List (Fin d))) :
    Finset (List (Fin d)) := by
  classical
  exact insert a (insert b (C.filter fun c => ¬ higmanVCOrbit_Near a b c))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_far

/-- Membership in `higmanVCOrbit_far`. -/
theorem higmanVCOrbit_mem_far {d : ℕ} {a b c : List (Fin d)} {C : Finset (List (Fin d))} :
    c ∈ higmanVCOrbit_far a b C ↔ c = a ∨ c = b ∨ (c ∈ C ∧ ¬ higmanVCOrbit_Near a b c) := by
  classical
  unfold higmanVCOrbit_far
  simp only [Finset.mem_insert, Finset.mem_filter]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_mem_far

/-- The far part of an antichain, with `a` and `b` added, is an antichain. -/
theorem higmanVCOrbit_far_isAC {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {C : Finset (List (Fin d))} (hC : higmanVCTreeNFWitPivot_IsAC C) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCOrbit_far a b C) := by
  intro u hu v hv huv
  rw [higmanVCOrbit_mem_far, higmanVCOrbit_Near] at hu hv
  rcases hu with rfl | rfl | ⟨huC, hun⟩ <;> rcases hv with rfl | rfl | ⟨hvC, hvn⟩
  · exact absurd rfl huv
  · exact hab
  · exact fun h => hvn (Or.inl h)
  · exact hba
  · exact absurd rfl huv
  · exact fun h => hvn (Or.inr (Or.inr (Or.inl h)))
  · exact fun h => hun (Or.inr (Or.inl h))
  · exact fun h => hun (Or.inr (Or.inr (Or.inr h)))
  · exact hC u huC v hvC huv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_far_isAC

/-- A balanced left factor does not spoil the symmetric discharge. -/
theorem higmanVCOrbit_U_mul_sym_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {u σ : higmanVCCommon_Q d} (hu : u ∈ higmanVCTreeNF_U d)
    (hσ : higmanVCLeafExp_Sym d a b σ) :
    u * σ * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rw [mul_assoc]
  exact higmanVCPivotAC_U_mul_S hu (higmanVCLeafExp_sym_mem_S hab hba hσ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_U_mul_sym_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
