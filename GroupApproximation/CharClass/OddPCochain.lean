import GroupApproximation.CharClass.OddPDiagonal
import GroupApproximation.CharClass.OddPEvalNatural
import GroupApproximation.CharClass.SteenrodCochain
import GroupApproximation.Meta.AxiomGuard

/-!
# The cochain operations `D_j` of the equivariant diagonal at odd `p`

For a cochain `u ∈ C^q(X; F_p)` and a `W`-index `j`, `D_j(u) ∈ C^{pq−j}(X; F_p)` evaluates the
`p`-fold tensor power `u^{⊗p}` on the diagonal of the generator `e_j ⊗ σ`:

  `D_j(u)(σ) = ⟨u^{⊗p}, Δ(e_j ⊗ σ)⟩`,   `σ` a singular `(pq − j)`-simplex.

The reduced powers are the classes of these cochains at the indices `j = (q − 2i)(p − 1)`.  This
file proves the two facts every later step uses:

* `oddD_cocycle` — **`D_j(u)` is a cocycle when `u` is.**  Evaluate `u^{⊗p}` on
  `Δ(d(e_j ⊗ σ'))`.  It is `0`, because `Δ` is a chain map and `u^{⊗p}` is a cocycle.  The
  resolution half of `d(e_j ⊗ σ')` is `T − 1` or the norm `1 + T + ⋯ + T^{p−1}` applied to a
  generator.  A constant tuple of single-degree cochains does not see `T` at odd `p`, so `T − 1`
  evaluates to `0` and the norm evaluates to `p · (…) = 0`.  What is left is the simplicial half,
  `(−1)^j` times `δ(D_j u)(σ')`.
* `oddD_natural` — **`D_j` commutes with pullback**, from the naturality of the diagonal and of the
  evaluation.

The additive map `oddEvalHom` (evaluate on the diagonal) carries the finite sums.  Its three
evaluation lemmas are stated for any tuple of cochains, for reuse by the additivity argument:
boundaries evaluate to zero against cocycles (`oddEvalHom_oddDiff_eq_zero`), a sign `(−1)^e` of the
group ring comes out as a sign of `F_p` (`oddEvalHom_neg_one_pow_smul`), and the simplicial half of
the differential evaluates as a coboundary (`oddEvalHom_oddDiffS_succ`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Evaluation on the diagonal -/

/-- **Evaluation on the diagonal**: `x ↦ ⟨φ, Δ x⟩`, additive in `x`. -/
def oddEvalHom (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0}) (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) : OddWTensor p k X →+ ZMod p :=
  AddMonoidHom.mk' (fun x => tupEval (ZMod p) X p k φ (oddDiagApp p X k x))
    fun x y => (congrArg (tupEval (ZMod p) X p k φ) (oddDiagApp_add p X k x y)).trans
      (map_add _ _ _)

@[simp] theorem oddEvalHom_apply (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0}) (k : ℕ)
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (x : OddWTensor p k X) :
    oddEvalHom p X k φ x = tupEval (ZMod p) X p k φ (oddDiagApp p X k x) :=
  rfl

/-- A single cocycle, placed in its degree, has vanishing graded coboundary. -/
theorem gCoboundary_piSingle_eq_zero (K : Type) [CommRing K] {X : TopCat.{0}} {q : ℕ}
    (u : singularCochainGroup K X q) (hu : cochainCoboundary K X q u = 0) :
    gCoboundary K X (Pi.single q u) = 0 := by
  funext n
  show gCoboundary K X (Pi.single q u) n = 0
  cases n with
  | zero => exact gCoboundary_zero K (Pi.single q u)
  | succ n =>
    rw [gCoboundary_succ]
    by_cases h : n = q
    · subst h
      rw [Pi.single_eq_same]
      exact hu
    · rw [Pi.single_eq_of_ne h]
      unfold cochainCoboundary
      exact map_zero _

/-- **Boundaries evaluate to zero against cocycles.**  The diagonal is a chain map (`oddDiagApp_d`)
and a tuple of cocycles kills tuple boundaries (`tupEval_tupD_eq_zero`). -/
theorem oddEvalHom_oddDiff_eq_zero (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}}
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n)
    (hφ : ∀ l, gCoboundary (ZMod p) X (φ l) = 0) (k : ℕ) (x : OddWTensor p (k + 1) X) :
    oddEvalHom p X k φ (oddDiff p (oddSingularBoundary p) X k x) = 0 := by
  rw [oddEvalHom_apply, ← oddDiagApp_d]
  exact tupEval_tupD_eq_zero (ZMod p) φ hφ k _

/-- A sign of the group ring leaves the evaluation as the same sign of `F_p`. -/
theorem oddEvalHom_neg_one_pow_smul (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}}
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (k e : ℕ) (x : OddWTensor p k X) :
    oddEvalHom p X k φ ((-1 : GroupRingZMod p) ^ e • x)
      = (-1 : ZMod p) ^ e * oddEvalHom p X k φ x := by
  rcases Nat.even_or_odd e with he | he
  · rw [he.neg_one_pow, he.neg_one_pow, one_smul, one_mul]
  · rw [he.neg_one_pow, he.neg_one_pow, neg_one_smul, map_neg, neg_one_mul]

/-! ## 2. The resolution half of the differential -/

/-- **The resolution coefficients kill a constant tuple at odd `p`.**  The coefficient is `T − 1`
or the norm; the first evaluates to `0` because the constant tuple does not see `T`, the second to
`p · (…) = 0`. -/
theorem oddEvalHom_altCoeff_smul (p : ℕ) [NeZero p] [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}}
    (ψ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (q : ℕ) (hq : ∀ n, n ≠ q → ψ n = 0)
    (k i : ℕ) (x : OddWTensor p k X) :
    oddEvalHom p X k (fun _ => ψ) (altCoeff (grS p) (grNorm p) i • x) = 0 := by
  have hgen1 : ∀ y : tupMod (ZMod p) X p k,
      galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) (grGen p) y
        = (tupT (ZMod p) X p k ^ 1) y :=
    fun y => moduleOfOrderP_smul (Fact.out : p.Prime).one_lt _ _ y
  have hgen : galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
      (grGen p) = tupT (ZMod p) X p k :=
    LinearMap.ext fun y => (hgen1 y).trans
      (congrArg (fun τ : Module.End (ZMod p) (tupMod (ZMod p) X p k) => τ y) (pow_one _))
  rw [oddEvalHom_apply, oddDiagApp_smul]
  by_cases he : Even i
  · rw [altCoeff_even _ _ he, grS, map_sub, map_one, hgen, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, tupEval_tupT_const (ZMod p) hp ψ q hq, sub_self]
  · rw [altCoeff_odd _ _ he, grNorm, map_sum, LinearMap.sum_apply, map_sum]
    simp only [map_pow, hgen]
    rw [tupEval_sum_tupT_pow (ZMod p) hp ψ q hq, ZMod.natCast_self, zero_mul]

/-- **The resolution half of the differential evaluates to zero** against a constant tuple of
single-degree cochains at odd `p`. -/
theorem oddEvalHom_oddDiffW (p : ℕ) [NeZero p] [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}}
    (ψ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (q : ℕ) (hq : ∀ n, n ≠ q → ψ n = 0)
    (k : ℕ) (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) :
    oddEvalHom p X k (fun _ => ψ) (oddDiffW p X k n σ) = 0 := by
  induction n using Fin.lastCases with
  | last => rw [oddDiffW_last, map_zero]
  | cast j =>
    rw [oddDiffW_castSucc]
    exact oddEvalHom_altCoeff_smul p hp ψ q hq k _ _

/-! ## 3. The simplicial half of the differential -/

/-- The differential on a generator splits into its resolution half and its simplicial half. -/
theorem oddEvalHom_oddDiff_single (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}}
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    oddEvalHom p X k φ (oddDiff p (oddSingularBoundary p) X k
        (Finsupp.single (⟨n, σ⟩ : WSIndex (k + 1) X) (1 : GroupRingZMod p)))
      = oddEvalHom p X k φ (oddDiffW p X k n σ)
        + oddEvalHom p X k φ (oddDiffS p (oddSingularBoundary p) X k n σ) := by
  rw [oddDiff_single, oddDiffGen, map_add]

/-- **The simplicial half evaluates as a coboundary**: the Koszul sign `(−1)^{k − m}` times the
alternating sum over the faces of `σ`. -/
theorem oddEvalHom_oddDiffS_succ (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}}
    (φ : Fin p → ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (k : ℕ) (m : Fin (k + 1))
    (σ : singularSimplices X (m.val + 1)) :
    oddEvalHom p X k φ
        (oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) (simplexEquiv X (m.val + 1) σ))
      = (-1 : ZMod p) ^ (k - m.val) * ∑ i : Fin (m.val + 2), (-1 : ZMod p) ^ (i : ℕ) *
          oddEvalHom p X k φ (Finsupp.single
            (⟨m, simplexEquiv X m.val (faceSimplex X m.val i σ)⟩ : WSIndex k X) 1) := by
  rw [oddDiffS_succ, oddEvalHom_neg_one_pow_smul]
  congr 1
  -- The evaluation, pulled back to the singular chains of the face degree.
  let Ψ : ((singFreeR (GroupRingZMod p)).obj X).X m.val →+ ZMod p :=
    (oddEvalHom p X k φ).comp
      ((Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
          (fun τ : stdSimplexTop m.val ⟶ X => (⟨m, τ⟩ : WSIndex k X))).toAddMonoidHom.comp
        (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
          (simplexEquiv X m.val)).toAddMonoidHom)
  have hd := congrArg Ψ (singFreeR_d_single (GroupRingZMod p) X m.val σ)
  rw [map_sum] at hd
  have hsingle : Finsupp.mapDomain (simplexEquiv X (m.val + 1)).symm
      (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZMod p))
        = Finsupp.single σ 1 := by
    rw [Finsupp.mapDomain_single, Equiv.symm_apply_apply]
  refine Eq.trans ?_ (hd.trans (Finset.sum_congr rfl fun i _ => ?_))
  · exact congrArg (fun c => Ψ ((((singFreeR (GroupRingZMod p)).obj X).d (m.val + 1) m.val).hom c))
      hsingle
  · rw [map_zsmul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    congr 1
    show oddEvalHom p X k φ (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ : stdSimplexTop m.val ⟶ X => (⟨m, τ⟩ : WSIndex k X))
        (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X m.val)
          (Finsupp.single (faceSimplex X m.val i σ) 1))) = _
    rw [Finsupp.lmapDomain_apply (simplexEquiv X m.val), Finsupp.mapDomain_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ## 4. The cochains `D_j` -/

/-- **`D_j(u)`**: the cochain `σ ↦ ⟨u^{⊗p}, Δ(e_j ⊗ σ)⟩` on singular `(pq − j)`-simplices.  The
generator `e_j ⊗ σ` of `W ⊗ C(X)` in total degree `pq` has simplex degree `pq − j`. -/
def oddD (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}} (q j : ℕ)
    (u : singularCochainGroup (ZMod p) X q) : singularCochainGroup (ZMod p) X (p * q - j) :=
  cochainOfFun (p * q - j) fun σ =>
    tupEval (ZMod p) X p (p * q) (fun _ => Pi.single q u)
      (oddDiagApp p X (p * q)
        (Finsupp.single (⟨⟨p * q - j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
          simplexEquiv X (p * q - j) σ⟩ : WSIndex (p * q) X) (1 : GroupRingZMod p)))

/-- The value of `D_j(u)` on a simplex. -/
theorem oddD_eval (p : ℕ) [NeZero p] [Fact p.Prime] {X : TopCat.{0}} (q j : ℕ)
    (u : singularCochainGroup (ZMod p) X q) (τ : singularSimplices X (p * q - j)) :
    cochainEval (p * q - j) (oddD p q j u) τ
      = tupEval (ZMod p) X p (p * q) (fun _ => Pi.single q u)
          (oddDiagApp p X (p * q)
            (Finsupp.single (⟨⟨p * q - j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
              simplexEquiv X (p * q - j) τ⟩ : WSIndex (p * q) X) (1 : GroupRingZMod p))) := by
  unfold oddD
  exact cochainEval_cochainOfFun _ _ τ

/-- **R2. `D_j(u)` is a cocycle when `u` is.**  The hypothesis `j ≤ pq` is not needed by the
proof and is kept only to match the interface consumers were written against. -/
theorem oddD_cocycle (p : ℕ) [NeZero p] [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ)
    (_hj : j ≤ p * q) (u : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) :
    cochainCoboundary (ZMod p) X (p * q - j) (oddD p q j u) = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainEval_zero, cochainCoboundary_eval]
  have hlt : p * q - j < p * q + 1 := Nat.lt_succ_of_le (Nat.sub_le _ _)
  have hq : ∀ n, n ≠ q → (Pi.single q u : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) n = 0 :=
    fun n hn => by rw [Pi.single_eq_of_ne hn]
  have h0 := oddEvalHom_oddDiff_eq_zero p (fun _ => Pi.single q u)
    (fun _ => gCoboundary_piSingle_eq_zero (ZMod p) u hu) (p * q)
    (Finsupp.single (⟨Fin.succ (⟨p * q - j, hlt⟩ : Fin (p * q + 1)),
      simplexEquiv X (p * q - j + 1) σ⟩ : WSIndex (p * q + 1) X) (1 : GroupRingZMod p))
  rw [oddEvalHom_oddDiff_single, oddEvalHom_oddDiffW p hp _ q hq, zero_add,
    oddEvalHom_oddDiffS_succ p _ (p * q) ⟨p * q - j, hlt⟩ σ] at h0
  have hS := ((isUnit_neg_one (α := ZMod p)).pow
    (p * q - (⟨p * q - j, hlt⟩ : Fin (p * q + 1)).val)).mul_right_eq_zero.mp h0
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hS
  rw [oddD_eval]
  rfl

/-- A single cochain placed in its degree pulls back degreewise. -/
theorem piSingle_cochainPullback_apply (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (q : ℕ) (u : singularCochainGroup K Y q) (n : ℕ) :
    cochainPullback f n ((Pi.single q u : ∀ n : ℕ, singularCochainGroup K Y n) n)
      = (Pi.single q (cochainPullback f q u) : ∀ n : ℕ, singularCochainGroup K X n) n := by
  by_cases h : n = q
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
    unfold cochainPullback
    exact map_zero _

/-- **R3. `D_j` commutes with pullback.** -/
theorem oddD_natural (p : ℕ) [NeZero p] [Fact p.Prime] {X Y : TopCat.{0}} (f : X ⟶ Y) (q j : ℕ)
    (u : singularCochainGroup (ZMod p) Y q) :
    cochainPullback f (p * q - j) (oddD p q j u) = oddD p q j (cochainPullback f q u) := by
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, oddD_eval, oddD_eval]
  have hgen : (Finsupp.single (⟨⟨p * q - j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
        simplexEquiv Y (p * q - j)
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk (p * q - j))) τ)⟩ :
          WSIndex (p * q) Y) (1 : GroupRingZMod p))
      = Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f (p * q))
          (Finsupp.single (⟨⟨p * q - j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
            simplexEquiv X (p * q - j) τ⟩ : WSIndex (p * q) X) (1 : GroupRingZMod p)) := by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rfl
  rw [hgen, ← oddDiagApp_natural, tupEval_tupMap]
  exact congrArg (fun φ => tupEval (ZMod p) X p (p * q) φ _)
    (funext fun (_ : Fin p) => funext fun (n : ℕ) =>
      piSingle_cochainPullback_apply (ZMod p) f q u n)

/-! ## 5. The axiom closure -/

#audit_axioms oddEvalHom_oddDiff_eq_zero
#audit_axioms oddEvalHom_oddDiffS_succ
#audit_axioms oddD_cocycle
#audit_axioms oddD_natural

end

end GroupApproximation.CharClass
