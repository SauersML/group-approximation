import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommOptions
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent graph of a pair and its square edges (lane bh-met-77o)

Fix an incomparable pair `A = (x, y)` of level `n = |x| + |y|`.  A **node** of `A` is a short
incomparable pair `w = (P, Q)` whose cone swap carries `A` to a pair `C_w = (X, Y)` of smaller
level (`higmanVCTauTight_Node`); the node is **good** when the identity
`ψ(w) · ψ(A) · ψ(w)⁻¹ = ψ(C_w)` holds (`higmanVCTauShort_conjEq d P Q x y X Y`).

An **edge** `w₁ → w₂` (`higmanVCTauTight_Edge`) asks that the cone swap `w₁` carry both words of
`w₂` to short words and carry `C_{w₂}` to a pair `E` of level `< n`.  Then, using only
instances strictly below level `n` (`higmanVCTauShort_Below d n`):

* `higmanVCTauTight_fwd`: `w₁` good ⇒ `w₂` good (square B of lane bh-met-77m, through `w₁`);
* `higmanVCTauTight_bwd`: `w₂` good ⇒ `w₁` good (square A of lane bh-met-77m, conjugator `w₁`).

So goodness spreads along edges in both directions (`higmanVCTauTight_link_good`).  The
canonical descent pair and its reverse are good by definition of `τ`
(`higmanVCTauTight_root_good`, from `higmanVCTauShort_optionE` and `higmanVCTauComm_erev`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `(P, Q)` is a short incomparable pair whose cone swap carries `x ↦ X` and `y ↦ Y`. -/
def higmanVCTauTight_Step (d : ℕ) (P Q x y X Y : List (Fin d)) : Prop :=
  ∃ (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P), P.length ≤ 3 ∧ Q.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) x X ∧ MapsCone (coneSwap P Q hPQ hQP) y Y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_Step

/-- A node of the descent graph of `(x, y)`: a short pair descending `(x, y)` to `(X, Y)`. -/
def higmanVCTauTight_Node (d : ℕ) (x y P Q X Y : List (Fin d)) : Prop :=
  higmanVCTauTight_Step d P Q x y X Y ∧ X.length + Y.length < x.length + y.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_Node

/-- An edge `(P, Q) → (R, S)` at level `n`, where `(R, S)` descends to `(U, V)`: the cone swap
`(P Q)` carries `R, S` to short words and `(U, V)` to a pair of level `< n`. -/
def higmanVCTauTight_Edge (d n : ℕ) (P Q R S U V : List (Fin d)) : Prop :=
  ∃ R1 S1 E1 E2 : List (Fin d), higmanVCTauTight_Step d P Q R S R1 S1 ∧
    R1.length ≤ 3 ∧ S1.length ≤ 3 ∧ higmanVCTauTight_Step d P Q U V E1 E2 ∧
    E1.length + E2.length < n

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_Edge

/-- A link between two nodes: equal, or an edge in either direction. -/
def higmanVCTauTight_Link (d n : ℕ) (P Q X Y R S U V : List (Fin d)) : Prop :=
  (P = R ∧ Q = S ∧ X = U ∧ Y = V) ∨ higmanVCTauTight_Edge d n P Q R S U V ∨
    higmanVCTauTight_Edge d n R S P Q X Y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_Link

/-- **Forward edge** (square B): the source node good gives the target node good. -/
theorem higmanVCTauTight_fwd {d : ℕ} (hd : 1 < d) {n : ℕ} (hB : higmanVCTauShort_Below d n)
    {x y P Q X Y R S U V : List (Fin d)} (hA : x.length + y.length = n)
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hN1 : higmanVCTauTight_Node d x y P Q X Y) (hN2 : higmanVCTauTight_Node d x y R S U V)
    (hE : higmanVCTauTight_Edge d n P Q R S U V)
    (g : higmanVCTauShort_conjEq d P Q x y X Y) : higmanVCTauShort_conjEq d R S x y U V := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨⟨hPQ, hQP, hP, hQ, hxX, hyY⟩, hC1⟩ := hN1
  obtain ⟨⟨hRS, hSR, hR, hS, hxU, hyV⟩, hC2⟩ := hN2
  obtain ⟨R1, S1, E1, E2, ⟨_, _, _, _, hwR, hwS⟩, hR1, hS1, ⟨_, _, _, _, hUE, hVE⟩, hEn⟩ := hE
  have hss := coneSwap_mul_self hPQ hQP
  have hrr := coneSwap_mul_self hRS hSR
  have hUx := higmanVCTauConj_mapsCone_symm hxU hrr
  have hVy := higmanVCTauConj_mapsCone_symm hyV hrr
  have hUV : ¬ U <+: V := higmanVCTauConj_not_prefix_of_maps hUx hVy hxy
  have hVU : ¬ V <+: U := higmanVCTauConj_not_prefix_of_maps hVy hUx hyx
  have e0 : higmanVCTauShort_conjEq d P Q X Y x y := higmanVCTauComm_flip_eq hP hQ g
  have h1 : higmanVCTauShort_Inst d R1 S1 X Y E1 E2 := hB R1 S1 X Y E1 E2 (by omega) hEn
  have h2 : higmanVCTauShort_Inst d P Q E1 E2 U V := hB P Q E1 E2 U V hEn (by omega)
  exact higmanVCTauComm_squareB hd hRS hSR hR hS hPQ hQP hP hQ
    (higmanVCTauConj_mapsCone_symm hxX hss) (higmanVCTauConj_mapsCone_symm hyY hss)
    hxU hyV hxy hyx hUV hVU hwR hwS hR1 hS1 hUE hVE e0 h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_fwd

/-- **Backward edge** (square A): the target node good gives the source node good. -/
theorem higmanVCTauTight_bwd {d : ℕ} (hd : 1 < d) {n : ℕ} (hB : higmanVCTauShort_Below d n)
    {x y P Q X Y R S U V : List (Fin d)} (hA : x.length + y.length = n)
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hN1 : higmanVCTauTight_Node d x y P Q X Y) (hN2 : higmanVCTauTight_Node d x y R S U V)
    (hE : higmanVCTauTight_Edge d n P Q R S U V)
    (g : higmanVCTauShort_conjEq d R S x y U V) : higmanVCTauShort_conjEq d P Q x y X Y := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨⟨hPQ, hQP, hP, hQ, hxX, hyY⟩, hC1⟩ := hN1
  obtain ⟨⟨hRS, hSR, hR, hS, hxU, hyV⟩, hC2⟩ := hN2
  obtain ⟨R1, S1, E1, E2, ⟨_, _, _, _, hwR, hwS⟩, hR1, hS1, ⟨_, _, _, _, hUE, hVE⟩, hEn⟩ := hE
  have hss := coneSwap_mul_self hPQ hQP
  have hrr := coneSwap_mul_self hRS hSR
  have hXx := higmanVCTauConj_mapsCone_symm hxX hss
  have hYy := higmanVCTauConj_mapsCone_symm hyY hss
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have e0 : higmanVCTauShort_conjEq d R S U V x y := higmanVCTauComm_flip_eq hR hS g
  have h1 : higmanVCTauShort_Inst d P Q U V E1 E2 := hB P Q U V E1 E2 (by omega) hEn
  have h2 : higmanVCTauShort_Inst d R1 S1 E1 E2 X Y := hB R1 S1 E1 E2 X Y hEn (by omega)
  exact higmanVCTauComm_squareA hd hPQ hQP hP hQ hRS hSR hR hS
    (higmanVCTauConj_mapsCone_symm hxU hrr) (higmanVCTauConj_mapsCone_symm hyV hrr)
    hxX hyY hxy hyx hXY hYX hwR hwS hR1 hS1 hUE hVE e0 h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_bwd

/-- **Links spread goodness** (in both directions, below level `n` only). -/
theorem higmanVCTauTight_link_good {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) {x y P Q X Y R S U V : List (Fin d)}
    (hA : x.length + y.length = n) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hN1 : higmanVCTauTight_Node d x y P Q X Y) (hN2 : higmanVCTauTight_Node d x y R S U V)
    (hL : higmanVCTauTight_Link d n P Q X Y R S U V)
    (g : higmanVCTauShort_conjEq d P Q x y X Y) : higmanVCTauShort_conjEq d R S x y U V := by
  rcases hL with ⟨rfl, rfl, rfl, rfl⟩ | hE | hE
  · exact g
  · exact higmanVCTauTight_fwd hd hB hA hxy hyx hN1 hN2 hE g
  · exact higmanVCTauTight_bwd hd hB hA hxy hyx hN2 hN1 hE g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_link_good

/-- **Roots.**  The canonical descent pair of a long pair, and its reverse, are good nodes
(definition of `τ`: `higmanVCTauShort_optionE`, `higmanVCTauComm_erev`). -/
theorem higmanVCTauTight_root_good {d : ℕ} (hd : 1 < d) {x y P Q X Y : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3)) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hroot : (P = higmanVCTau_pP (x, y) ∧ Q = higmanVCTau_pQ (x, y)) ∨
      (P = higmanVCTau_pQ (x, y) ∧ Q = higmanVCTau_pP (x, y)))
    (hN : higmanVCTauTight_Node d x y P Q X Y) : higmanVCTauShort_conjEq d P Q x y X Y := by
  obtain ⟨⟨hPQ, hQP, _, _, hxX, hyY⟩, _⟩ := hN
  rcases hroot with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hE : higmanVCTauShort_OptionE d (higmanVCTau_pP (x, y)) (higmanVCTau_pQ (x, y)) x y := by
      unfold higmanVCTauShort_OptionE
      exact ⟨hlong, rfl, rfl⟩
    exact higmanVCTauShort_optionE hd hPQ hQP hE hxy hyx hxX hyY
  · exact higmanVCTauComm_erev hd hlong hPQ hQP hxy hyx hxX hyY

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_root_good

end GroupApproximation.BooneHigman.Metabelian.Envelope
