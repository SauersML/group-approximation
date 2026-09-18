import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJRedEuclid
import GroupApproximation.Meta.AxiomGuard

/-!
# The `J`-reduction of the root check, part 3: the residual

Lane `bh-met-94a`, gap (b) of `ElemFPK2PolyNagaoRootMain`: the orbit vectors with a nonzero
coordinate in `J = K \ {m}`.  Notation of `ElemFPK2PolyNagaoJRedMove`.

* `k2PolyNagaoJRed_TorusAt p`: the check of `σ` at `y = x_mL(1)` at every supported orbit
  vector (supported on `{m, L}`).  `k2PolyNagaoJRed_TorusIface` is this for every prime `p`.
  **It is the interface for lane 94b** (torus scaling of the representatives).  For `p = 2` it
  is PROVED here (`k2PolyNagaoJRed_torusAt_two`).
* `k2PolyNagaoJRed_ResAt p`: the check at the **residual normal forms**, the orbit vectors `v`
  with, for some `j ∈ J`:
  - `v` supported on `{m, L, j}`;
  - `v j ≠ 0`;
  - `deg v_m < deg v_j` and `deg v_L < deg v_j`.

  `k2PolyNagaoJRed_Statement` (**the residual**) is this for every prime `p`.
* `k2PolyNagaoJRed_check_of_at`: `ResAt p` and `TorusAt p` give the check of `σ` at `y`.
  This is the Euclidean `J`-reduction (`k2PolyNagaoJRed_check_all`).  Every move is a root of
  `Q^m`, and the check moves back along it by the cocycle transfer.
* `k2PolyNagaoJRed_wide_of_statement`, `k2PolyNagaoJRed_root_of_statement`: the residual plus
  `TorusIface` give `k2PolyNagaoWide_Statement` and `k2PolyNagaoRoot_Statement`.
* `k2PolyNagaoJRed_check_two`: **for `p = 2`, `ResAt 2` alone gives the check.**
* `k2PolyNagaoJRed_torusIface_of_odd`: `TorusIface` needs only the odd primes.

**LOUD: the residual is NOT proved here.  It is TRUE, and it is logically EQUIVALENT to
`k2PolyNagaoWide_Statement`: both directions are proved below
(`_wide_of_statement` with `_torusIface_of_wide`, and `_statement_of_wide`), and the converse
is a trivial restriction.  EXPECT IT TO BE PARKED.  It is strictly smaller only in proof
content.**  An arbitrary number of nonzero `J`-coordinates is reduced to a single one, in
Euclidean normal form against `m` and `L`.

**Why nothing smaller comes from `Q^m` alone.**  The moves of `Q^m` (roots `x_ij`,
`i ∈ K ∪ {L}`, `j ∈ J`) never change the `E_J`-class of `v_J`, and in particular they keep its
gcd.  So they can never reach the supported case from `v_J ≠ 0`, and the residual class is
nonempty: `e_L + X e_j = x_jL(X) e_L` is already in normal form.  The remaining roots `x_jm`
and `x_Lm` conjugate `y` into checks at `x_jL`, which is circular.

**Truth.**  The residual is implied by the true `k2PolyNagaoWide_Statement` (lane 93l).  The
scratchpad script `bh-met-94a/chk.py` (reusing `bh-met-93v/chk.py`) checks, over `F_2`, `F_3`
and `F_5` with `(|I|, |K|) ∈ {(4,2), (5,3), (6,4)}`:
- the conjugation shadow: `y x_ij(a) y⁻¹` is in the `Q`-shadow;
- that the Euclidean `J`-reduction terminates in the normal form;
- that the `J`-gcd is invariant.

It prints ALL OK.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec)

/-- **The torus interface at `p`** (lane 94b's target): the check of `σ` at `x_mL(1)` at every
supported orbit vector.  TRUE (a restriction of `k2PolyNagaoWide_Statement`).  PROVED for
`p = 2` (`k2PolyNagaoJRed_torusAt_two`). -/
def k2PolyNagaoJRed_TorusAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L : I)
    (hmL : m ≠ L), L ∉ K → m ∈ K → (∃ i ∈ K, i ≠ m) → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    k2PolyNagaoWide_Stab p (K.erase m) m →
    ∀ v : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
      k2PolyNagaoWide_Supp m L v →
      (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
          x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
        k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_TorusAt

/-- **The torus interface** (lane 94b): `k2PolyNagaoJRed_TorusAt p` for every prime `p`. -/
def k2PolyNagaoJRed_TorusIface : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], k2PolyNagaoJRed_TorusAt p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_TorusIface

/-- **The residual at `p`**: the check of `σ` at `x_mL(1)` at the residual normal forms.  These
are the orbit vectors `v` supported on `{m, L, j}` for some `j ∈ K \ {m}`, with `v j ≠ 0` and
`deg v_m, deg v_L < deg v_j`. -/
def k2PolyNagaoJRed_ResAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L : I)
    (hmL : m ≠ L), L ∉ K → m ∈ K → (∃ i ∈ K, i ≠ m) → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    k2PolyNagaoWide_Stab p (K.erase m) m →
    ∀ v : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
      ∀ j ∈ K.erase m, (∀ k, k ≠ m → k ≠ L → k ≠ j → v k = 0) → v j ≠ 0 →
      (v m).degree < (v j).degree → (v L).degree < (v j).degree →
      (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
          x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
        k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_ResAt

/-- **The residual of lane `bh-met-94a`**: `k2PolyNagaoJRed_ResAt p` for every prime `p`.
TRUE.  LOUD: logically EQUIVALENT to `k2PolyNagaoWide_Statement` (module docstring), and
strictly smaller only in proof content.  Expect it to be PARKED. -/
def k2PolyNagaoJRed_Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], k2PolyNagaoJRed_ResAt p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_Statement

/-- **The `J`-reduction at `p`.**  The residual at `p` and the torus interface at `p` give the
check of `σ` at `x_mL(1)` (`k2PolyNagaoJRed_check_all`). -/
theorem k2PolyNagaoJRed_check_of_at {p : ℕ} [Fact p.Prime] (hR : k2PolyNagaoJRed_ResAt p)
    (hT : k2PolyNagaoJRed_TorusAt p) {I : Type} [Fintype I] [DecidableEq I] (K : Finset I)
    (m L : I) (hmL : m ≠ L) (hLK : L ∉ K) (hmK : m ∈ K) (him : ∃ i ∈ K, i ≠ m)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hSK : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    (hJ : k2PolyNagaoWide_Stab p (K.erase m) m) :
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p))) :=
  k2PolyNagaoJRed_check_all hmL hmK hLK hthird hJ
    (fun w hw hS => hT K m L hmL hLK hmK him hthird hconst hSK hJ w hw hS)
    (fun w hw j hj h0 h1 h2 h3 =>
      hR K m L hmL hLK hmK him hthird hconst hSK hJ w hw j hj h0 h1 h2 h3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_check_of_at

/-- The residual and the torus interface give `k2PolyNagaoWide_Statement`. -/
theorem k2PolyNagaoJRed_wide_of_statement (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) : k2PolyNagaoWide_Statement := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst hSK hJ
  exact k2PolyNagaoJRed_check_of_at (hR p) (hT p) K m L hmL hLK hmK him hthird hconst hSK hJ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_wide_of_statement

/-- **The endpoint of lane `bh-met-94a`**: the residual and the torus interface give the
residual `k2PolyNagaoRoot_Statement` of lane 93v. -/
theorem k2PolyNagaoJRed_root_of_statement (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) : k2PolyNagaoRoot_Statement :=
  k2PolyNagaoRoot_statement_of_wide (k2PolyNagaoJRed_wide_of_statement hR hT)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_root_of_statement

/-- **The torus interface at `p = 2` is PROVED**: over `F_2` every supported orbit vector is in
the easy class of lane 93v, where the check is `k2PolyNagaoRoot_check_supp`. -/
theorem k2PolyNagaoJRed_torusAt_two : k2PolyNagaoJRed_TorusAt 2 := by
  intro I _ _ K m L hmL hLK hmK _ hthird hconst _ hJ v hv hS
  have hE := k2PolyNagaoRoot_easy_of_units k2PolyNagaoRoot_units_two hmL hmK hLK hv hS
  exact k2PolyNagaoRoot_check_supp hmL hmK hLK hthird hconst hJ hv hE.1 hE.2.1 hE.2.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_torusAt_two

/-- **For `p = 2` the residual at `2` alone gives the check of `σ` at `x_mL(1)`.** -/
theorem k2PolyNagaoJRed_check_two (hR : k2PolyNagaoJRed_ResAt 2) {I : Type} [Fintype I]
    [DecidableEq I] (K : Finset I) (m L : I) (hmL : m ≠ L) (hLK : L ∉ K) (hmK : m ∈ K)
    (him : ∃ i ∈ K, i ≠ m) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod 2 →+* Polynomial (ZMod 2))).range,
      g ∈ K2 I (Polynomial (ZMod 2)) → g = 1)
    (hSK : ∀ s ∈ k2PolyDeg_S 2 K, s ∈ K2 I (Polynomial (ZMod 2)) → s = 1)
    (hJ : k2PolyNagaoWide_Stab 2 (K.erase m) m) :
    k2PolyEuclid_Check 2 K L (k2PolyNagaoWide_sigma 2 K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod 2))) :=
  k2PolyNagaoJRed_check_of_at hR k2PolyNagaoJRed_torusAt_two K m L hmL hLK hmK him hthird
    hconst hSK hJ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_check_two

/-- `TorusIface` needs only the odd primes (`p = 2` is `k2PolyNagaoJRed_torusAt_two`). -/
theorem k2PolyNagaoJRed_torusIface_of_odd
    (h : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → k2PolyNagaoJRed_TorusAt p) :
    k2PolyNagaoJRed_TorusIface := by
  intro p _
  by_cases hp : p = 2
  · subst hp
    exact k2PolyNagaoJRed_torusAt_two
  · exact h p hp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_torusIface_of_odd

/-- The residual and the torus interface give `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoJRed_K2_bot_of_statement (hR : k2PolyNagaoJRed_Statement)
    (hT : k2PolyNagaoJRed_TorusIface) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoWide_K2_bot_of_statement (k2PolyNagaoJRed_wide_of_statement hR hT) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_K2_bot_of_statement

/-- The converse (LOUD: so the residual is logically EQUIVALENT to the wide statement). -/
theorem k2PolyNagaoJRed_statement_of_wide (hW : k2PolyNagaoWide_Statement) :
    k2PolyNagaoJRed_Statement := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst hSK hJ v hv _ _ _ _ _ _
  exact hW p K m L hmL hLK hmK him hthird hconst hSK hJ v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_statement_of_wide

/-- The torus interface is a restriction of the wide statement. -/
theorem k2PolyNagaoJRed_torusIface_of_wide (hW : k2PolyNagaoWide_Statement) :
    k2PolyNagaoJRed_TorusIface := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst hSK hJ v hv _
  exact hW p K m L hmL hLK hmK him hthird hconst hSK hJ v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_torusIface_of_wide

end GroupApproximation.BooneHigman.Metabelian.ElemFP
