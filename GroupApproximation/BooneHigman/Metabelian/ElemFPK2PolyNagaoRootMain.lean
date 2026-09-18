import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoRootCheck
import GroupApproximation.Meta.AxiomGuard

/-!
# The root check of the wide section, part 3: the residual

Lane `bh-met-93v`.  Notation of `ElemFPK2PolyNagaoRootCheck`; `y = x_mL(1)`,
`σ = k2PolyNagaoWide_sigma`, `r_v` the chosen representative of `v`.

* `k2PolyNagaoRoot_Easy p K m L hmL v`: `v` is supported on `{m, L}` and both `r_v` and
  `r_{yv}` keep the `m`-coordinate.  On this class the check of `σ` at `y` is PROVED
  (`k2PolyNagaoRoot_check_supp`).
* `k2PolyNagaoRoot_Statement` (**the residual**): `k2PolyNagaoWide_Statement` restricted to
  the orbit vectors outside the easy class.
* `k2PolyNagaoRoot_wide_of_statement`: the residual gives `k2PolyNagaoWide_Statement`.
* `k2PolyNagaoRoot_statement_of_wide`: the converse (trivial).
* `k2PolyNagaoRoot_easy_of_units`: when `(ZMod p)ˣ` is trivial, every supported orbit vector is
  easy.  `k2PolyNagaoRoot_units_two`: this holds for `p = 2`.
* `k2PolyNagaoRoot_K2_bot_of_statement`: the residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD: the residual is NOT proved here.  It is TRUE, and it is logically EQUIVALENT to
`k2PolyNagaoWide_Statement` (both directions are proved below).  It is STRICTLY SMALLER only
in proof content: it removes the easy orbit vectors, where the check is proved.**

What is proved:
- orbit transfer from `G_K` to `G_{{m}}` for supported vectors (the coprimality of `(v_m, v_L)`
  and the Euclidean orbit word);
- the rank-one Weyl check of lane 93d, transported to `Q_K`;
- the shift `q r = x_Lm(d) r` for `q ∈ Q` preserving the `m`-coordinate;
- the torus factor `(q r)_m = c r_m`, with `c` a unit constant.

What remains, and the two caveats:
- **(a) The choice of representative.**  For `p > 2` the easy class depends on the
  `Classical.epsilon` choice of `r_v`.  A choice can scale `r_m` by a constant unit
  `ε ≠ 1`, through a torus element `h_mi(ε) ∈ S_K`; the scratchpad script checks that such
  `(q, r)` exist.  So for `p > 2` the discharged class may be tiny, and nothing here proves
  it is nonempty.  What remains there is the torus equivariance of `σ₀` against `h_mi(ε)`.
- **(b) Non-supported vectors.**  For every `p`, the vectors `v` with a nonzero coordinate in
  `J = K \ {m}` are not treated.  These are the Euclidean `J`-reduction direction of `σ`.
- **For `p = 2`** (`_easy_of_units`, `_units_two`), the easy class is exactly the supported
  orbit vectors.  So the residual is only about the non-supported `v`.

**Truth.**  The residual is implied by the true `k2PolyNagaoWide_Statement` (lane 93l's
docstring).  The scratchpad script `bh-met-93v/chk.py` checks the matrix shadows over `F_2`,
`F_3` and `F_5`:
- the orbit coprimality;
- the orbit word;
- `(q r)_L = r_L + d r_m`;
- `q r = x_Lm(d) r`;
- the torus witness.

It prints ALL OK.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The easy class: `v` is supported on `{m, L}`, and the chosen representatives `r_v` and
`r_{yv}` (`y = x_mL(1)`) keep the `m`-coordinate. -/
def k2PolyNagaoRoot_Easy (p : ℕ) [Fact p.Prime] (K : Finset I) (m L : I) (hmL : m ≠ L)
    (v : I → Polynomial (ZMod p)) : Prop :=
  k2PolyNagaoWide_Supp m L v ∧ k2PolyNagaoWide_rep p K m L v m = v m ∧
    k2PolyNagaoWide_rep p K m L (act (x m L hmL (1 : Polynomial (ZMod p))) v) m =
      act (x m L hmL (1 : Polynomial (ZMod p))) v m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Easy

/-- **The residual of lane `bh-met-93v`.**  `k2PolyNagaoWide_Statement` at the orbit vectors
outside the easy class.  TRUE.  LOUD: it is logically EQUIVALENT to `k2PolyNagaoWide_Statement`
(`_wide_of_statement`, `_statement_of_wide`), and strictly smaller only in proof content.  For
`p > 2` the removed class depends on the choice of representative (module docstring). -/
def k2PolyNagaoRoot_Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L : I)
    (hmL : m ≠ L), L ∉ K → m ∈ K → (∃ i ∈ K, i ≠ m) → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    k2PolyNagaoWide_Stab p (K.erase m) m →
    ∀ v : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
      ¬ k2PolyNagaoRoot_Easy p K m L hmL v →
      (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
          x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
        k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Statement

/-- **The reduction.**  The residual gives `k2PolyNagaoWide_Statement`: on the easy class the
check is `k2PolyNagaoRoot_check_supp`. -/
theorem k2PolyNagaoRoot_wide_of_statement (hR : k2PolyNagaoRoot_Statement) :
    k2PolyNagaoWide_Statement := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst hSK hJ v hv
  by_cases hE : k2PolyNagaoRoot_Easy p K m L hmL v
  · exact k2PolyNagaoRoot_check_supp hmL hmK hLK hthird hconst hJ hv hE.1 hE.2.1 hE.2.2
  · exact hR p K m L hmL hLK hmK him hthird hconst hSK hJ v hv hE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_wide_of_statement

/-- The converse (LOUD: so the residual is logically equivalent to the wide statement). -/
theorem k2PolyNagaoRoot_statement_of_wide (hW : k2PolyNagaoWide_Statement) :
    k2PolyNagaoRoot_Statement := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst hSK hJ v hv _
  exact hW p K m L hmL hLK hmK him hthird hconst hSK hJ v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_statement_of_wide

/-- When `(ZMod p)ˣ` is trivial, every supported orbit vector is easy. -/
theorem k2PolyNagaoRoot_easy_of_units {p : ℕ} [Fact p.Prime] (h1 : ∀ β : (ZMod p)ˣ, β = 1)
    {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K) (hLK : L ∉ K)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoWide_Supp m L v) : k2PolyNagaoRoot_Easy p K m L hmL v :=
  ⟨hS, k2PolyNagaoRoot_rep_m hmL hmK hLK h1 hv hS,
    k2PolyNagaoRoot_rep_m hmL hmK hLK h1
      (k2PolyNF_orbit_act (k2PolyEuclid_x_mem_G hmL (1 : Polynomial (ZMod p))
        (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)) hv)
      (k2PolyNagaoRoot_supp_x hmL hS)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_easy_of_units

/-- `(ZMod 2)ˣ` is trivial. -/
theorem k2PolyNagaoRoot_units_two : ∀ β : (ZMod 2)ˣ, β = 1 := fun β => Subsingleton.elim β 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_units_two

/-- The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoRoot_K2_bot_of_statement (hR : k2PolyNagaoRoot_Statement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoWide_K2_bot_of_statement (k2PolyNagaoRoot_wide_of_statement hR) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_K2_bot_of_statement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
