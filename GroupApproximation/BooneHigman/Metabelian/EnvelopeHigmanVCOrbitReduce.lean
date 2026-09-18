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

/-- `h` is *a/b-balanced*: `h = ι r` for a word `r` in the letters of an antichain `C`, and
`π r` preserves the length of every leaf near the pivot `(a, b)`. -/
def higmanVCOrbit_Bal (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C ∧ ∃ r : FreeGroup (↥C × ↥C),
    higmanVCCommon_mk d (higmanVCAll_iota C r) = h ∧
      ∀ c : ↥C, higmanVCOrbit_Near a b c.1 → (higmanVCOrbit_pi C r c).1.length = c.1.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_Bal

/-- **a/b-balanced discharge.**  `h = u σ` with `u ∈ U` and `σ ∈ H_D` for
`D = {a, b} ∪ (far part of C)`, so `σ` is symmetric (trivial tree) and `h t ∈ S`. -/
theorem higmanVCOrbit_bal_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d} (hh : higmanVCOrbit_Bal d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨C, hC, r, rfl, hlen⟩ := hh
  have hK : ∀ x y : ↥C, ¬ higmanVCOrbit_Near a b x.1 → ¬ higmanVCOrbit_Near a b y.1 →
      higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) ∈
        higmanVCTreeNFWitPivot_H d (higmanVCOrbit_far a b C) := fun x y hx hy =>
    higmanVCLeafExp_letter_mem_H (higmanVCOrbit_mem_far.mpr (Or.inr (Or.inr ⟨x.2, hx⟩)))
      (higmanVCOrbit_mem_far.mpr (Or.inr (Or.inr ⟨y.2, hy⟩)))
  obtain ⟨u, hu, σ, hσ, heq⟩ :=
    higmanVCOrbit_split hC (fun c => higmanVCOrbit_Near a b c.1) hK _ r le_rfl hlen
  rw [heq]
  refine higmanVCOrbit_U_mul_sym_mem_S hab hba hu ⟨higmanVCOrbit_far a b C, {[]},
    higmanVCOrbit_far_isAC hab hba hC, higmanVCLeafExp_IsTree.root, hσ, fun e he => ?_⟩
  rw [Finset.mem_singleton] at he
  subst he
  simp only [List.append_nil]
  exact ⟨higmanVCOrbit_mem_far.mpr (Or.inl rfl),
    higmanVCOrbit_mem_far.mpr (Or.inr (Or.inl rfl))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_bal_mem_S

/-- `S` is closed under inverses. -/
theorem higmanVCOrbit_inv_mem_S {d : ℕ} {s : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) : s⁻¹ ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨u₂⁻¹, Subgroup.inv_mem _ hu₂, C, hC, h⁻¹,
    Subgroup.inv_mem _ hh, u₁⁻¹, Subgroup.inv_mem _ hu₁, by simp only [mul_inv_rev, mul_assoc]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_inv_mem_S

/-- **Twisted discharge.**  If `t⁻¹ h⁻¹ t⁻¹` is a/b-balanced, then `h t ∈ S`, because
`h t = ((t⁻¹ h⁻¹ t⁻¹) t)⁻¹`. -/
theorem higmanVCOrbit_twist_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbit_Bal d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have hs := higmanVCOrbit_inv_mem_S (higmanVCOrbit_bal_mem_S hab hba hh)
  rwa [inv_mul_cancel_right, mul_inv_rev, inv_inv, inv_inv] at hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_twist_mem_S

/-- The pivot closure of `higmanVCLeafExp_Closed`, required only for `h` that is
non-symmetric, not a/b-balanced and not twisted-balanced. -/
def higmanVCOrbit_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCLeafExp_Sym d a b h →
        ¬ higmanVCOrbit_Bal d a b h →
          ¬ higmanVCOrbit_Bal d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
            (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) →
            h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_Closed

/-- **Residual W'**: W restricted further to non-balanced, non-twisted-balanced `h`.
LOUD: `W' ⇔ W ⇔ Z` as Props.  W' is strictly smaller in proof content only. -/
def HigmanVCOrbitStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbit_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitStatement

/-- **`W' → W`.** -/
theorem higmanVCOrbit_W_of_orbit (hO : HigmanVCOrbitStatement) :
    HigmanVCLeafExpStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hO d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hM h hh hs
  by_cases hB : higmanVCOrbit_Bal d a b h
  · exact higmanVCOrbit_bal_mem_S hab hba hB
  by_cases hT : higmanVCOrbit_Bal d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ *
      h⁻¹ * (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)
  · exact higmanVCOrbit_twist_mem_S hab hba hT
  exact hcl C hC hL hM h hh hs hB hT

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_W_of_orbit

/-- **`W' → Z`.** -/
theorem higmanVCOrbit_Z_of_orbit (hO : HigmanVCOrbitStatement) : HigmanVCPivotYStatement :=
  higmanVCLeafExp_Z_of_W (higmanVCOrbit_W_of_orbit hO)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_Z_of_orbit

/-- **Wiring.**  `W'` and the short-relation section `τ` give the swap section. -/
theorem higmanVCOrbit_swapSection_of_orbit_of_tau (hO : HigmanVCOrbitStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCLeafExp_swapSection_of_W_of_tau (higmanVCOrbit_W_of_orbit hO) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_swapSection_of_orbit_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
