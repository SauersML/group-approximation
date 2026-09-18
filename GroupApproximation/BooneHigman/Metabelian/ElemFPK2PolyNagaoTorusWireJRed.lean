import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The Nagao torus wired into the `J`-reduction endpoints

Lane `bh-met-94d`, part 1 of 2 (a wiring lane: no new residual).  Lane 94b proved the torus
interface unconditionally (`k2PolyNagaoTorus_torusIface`, `k2PolyNagaoTorus_torusAt`).  Here it
is plugged into every endpoint of `ElemFPK2PolyNagaoJRedMain` that took it as a hypothesis:

* `k2PolyNagaoTorusWire_check_of_resAt`: `k2PolyNagaoJRed_check_of_at` without `hT`.
* `k2PolyNagaoTorusWire_wide_of_statement`: `k2PolyNagaoJRed_wide_of_statement` without `hT`.
* `k2PolyNagaoTorusWire_root_of_statement`: `k2PolyNagaoJRed_root_of_statement` without `hT`.
* `k2PolyNagaoTorusWire_K2_bot_of_statement`: `k2PolyNagaoJRed_K2_bot_of_statement` without
  `hT`.

The only remaining input is the lane-94a residual `k2PolyNagaoJRed_Statement`.  With the torus
proved, it is now logically equivalent, with no extra hypothesis, to `k2PolyNagaoWide_Statement`
and to `k2PolyNagaoRoot_Statement` (`k2PolyNagaoTorusWire_iff_wide`, `_iff_root`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The `J`-reduction at `p`, torus discharged**: the residual at `p` alone gives the check of
`σ` at `x_mL(1)` (`k2PolyNagaoJRed_check_of_at` with `k2PolyNagaoTorus_torusAt p`). -/
theorem k2PolyNagaoTorusWire_check_of_resAt {p : ℕ} [Fact p.Prime]
    (hR : k2PolyNagaoJRed_ResAt p) {I : Type} [Fintype I] [DecidableEq I] (K : Finset I)
    (m L : I) (hmL : m ≠ L) (hLK : L ∉ K) (hmK : m ∈ K) (him : ∃ i ∈ K, i ≠ m)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hSK : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    (hJ : k2PolyNagaoWide_Stab p (K.erase m) m) :
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p))) :=
  k2PolyNagaoJRed_check_of_at hR (k2PolyNagaoTorus_torusAt p) K m L hmL hLK hmK him hthird
    hconst hSK hJ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_check_of_resAt

/-- The lane-94a residual alone gives `k2PolyNagaoWide_Statement`. -/
theorem k2PolyNagaoTorusWire_wide_of_statement (hR : k2PolyNagaoJRed_Statement) :
    k2PolyNagaoWide_Statement :=
  k2PolyNagaoJRed_wide_of_statement hR k2PolyNagaoTorus_torusIface

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_wide_of_statement

/-- The lane-94a residual alone gives the lane-93v residual `k2PolyNagaoRoot_Statement`. -/
theorem k2PolyNagaoTorusWire_root_of_statement (hR : k2PolyNagaoJRed_Statement) :
    k2PolyNagaoRoot_Statement :=
  k2PolyNagaoJRed_root_of_statement hR k2PolyNagaoTorus_torusIface

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_root_of_statement

/-- **Nagao's theorem from the lane-94a residual alone**: `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoTorusWire_K2_bot_of_statement (hR : k2PolyNagaoJRed_Statement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoJRed_K2_bot_of_statement hR k2PolyNagaoTorus_torusIface hp hN

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_K2_bot_of_statement

/-- With the torus proved, the lane-94a residual is equivalent to `k2PolyNagaoWide_Statement`
(no side hypothesis). -/
theorem k2PolyNagaoTorusWire_iff_wide :
    k2PolyNagaoJRed_Statement ↔ k2PolyNagaoWide_Statement :=
  ⟨k2PolyNagaoTorusWire_wide_of_statement, k2PolyNagaoJRed_statement_of_wide⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_iff_wide

/-- With the torus proved, the lane-94a residual is equivalent to the lane-93v residual. -/
theorem k2PolyNagaoTorusWire_iff_root :
    k2PolyNagaoJRed_Statement ↔ k2PolyNagaoRoot_Statement :=
  ⟨k2PolyNagaoTorusWire_root_of_statement,
    fun h => k2PolyNagaoJRed_statement_of_wide (k2PolyNagaoRoot_wide_of_statement h)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorusWire_iff_root

end GroupApproximation.BooneHigman.Metabelian.ElemFP
