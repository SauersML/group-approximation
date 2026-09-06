import GroupApproximation.CharClass.SteenrodFourfoldBJunction

/-!
# The two degenerate branches of the chain-map identity

At a bidegree of the diagonal where one of the two simplices is a point the
Leibniz expansion collapses: every summand but one vanishes, and the one that
survives produces all three pieces of the answer by itself.

The two collapses are not mirror images.  When the *front* simplex is a point
only the summand at resolution index `0` survives, and it is the *right* block
that produces the swap term, because the swap acts trivially on a cochain of a
point.  When the *back* simplex is a point only the summand at index `i + 1`
survives, and it is the *left* block that produces everything, the surplus power
of the generator being absorbed by the same triviality.

Both branches are therefore the place where `swapEnd_phiAtDeg_degree_zero` is
spent, and neither is an instance of the generic branch.

## Main results

* `sum_tensorD_front_zero` — **the front-degenerate branch.**
* `sum_tensorD_back_zero` — **the back-degenerate branch.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## The face contributions, with the degree they carry left free -/

/-- The face contribution of the front simplex, the front degree free so that the
two spellings `M + 1 + p` and `M + (p + 1)` are reconciled by `congrArg`. -/
def faceLAt (X : TopCat.{0}) (k b p q M' : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) (A : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFour X k A b (∑ jj : Fin (M' + 2), phiAtDeg X A p (faceSimplex X M' jj ρ))
    ((groupRingGen ^ p) • phiAtDeg X b q τ)

theorem faceLAt_eq (X : TopCat.{0}) (k b p q M' : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) (A : ℕ) :
    faceLAt X k b p q M' ρ τ A
      = padFour X k A b (∑ jj : Fin (M' + 2), phiAtDeg X A p (faceSimplex X M' jj ρ))
          ((groupRingGen ^ p) • phiAtDeg X b q τ) := rfl

theorem faceLAt_congr (X : TopCat.{0}) (k b p q M' : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) {A A' : ℕ}
    (h : A = A') : faceLAt X k b p q M' ρ τ A = faceLAt X k b p q M' ρ τ A' :=
  congrArg (faceLAt X k b p q M' ρ τ) h

/-- The face contribution of the back simplex, the back degree free. -/
def faceRAt (X : TopCat.{0}) (k a p q M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) (B : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFour X k a B (phiAtDeg X a p ρ)
    ((groupRingGen ^ p) • ∑ jj : Fin (M'' + 2), phiAtDeg X B q (faceSimplex X M'' jj τ))

theorem faceRAt_eq (X : TopCat.{0}) (k a p q M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) (B : ℕ) :
    faceRAt X k a p q M'' ρ τ B
      = padFour X k a B (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) •
            ∑ jj : Fin (M'' + 2), phiAtDeg X B q (faceSimplex X M'' jj τ)) := rfl

theorem faceRAt_congr (X : TopCat.{0}) (k a p q M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) {B B' : ℕ}
    (h : B = B') : faceRAt X k a p q M'' ρ τ B = faceRAt X k a p q M'' ρ τ B' :=
  congrArg (faceRAt X k a p q M'' ρ τ) h

/-- The back junction, stated on the summand itself rather than on `bBack`, so
that it applies to a goal in which no abstraction is visible. -/
theorem bTerm_back_congr (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) {q q' : ℕ} (h : q = q') :
    bTerm X k a (d + q) p q ρ τ = bTerm X k a (d + q') p q' ρ τ :=
  bBack_congr X k a p ρ τ h

/-- The left face contribution read as a function of the back index alone. -/
def faceLBack (X : TopCat.{0}) (k p M' A : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) (q : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  faceLAt X k (d + q) p q M' ρ τ A

/-- The back junction for the left face contribution. -/
theorem faceLAt_back_congr (X : TopCat.{0}) (k p M' A : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) {q q' : ℕ} (h : q = q') :
    faceLAt X k (d + q) p q M' ρ τ A = faceLAt X k (d + q') p q' M' ρ τ A :=
  congrArg (faceLBack X k p M' A ρ τ) h

/-! ## The vanishings a point forces -/

theorem bTerm_front_pt (X : TopCat.{0}) (k a b p q : ℕ) {d : ℕ}
    (ρ : singularSimplices X 0) (τ : singularSimplices X d) (hp : 0 < p) :
    bTerm X k a b p q ρ τ = 0 := by
  rw [bTerm_eq, phiAtDeg_eq_zero_of_lt X a p 0 ρ hp, padFour_zero_left]

theorem bTerm_back_pt (X : TopCat.{0}) (k a b p q : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X 0) (hq : 0 < q) :
    bTerm X k a b p q ρ τ = 0 := by
  rw [bTerm_eq, phiAtDeg_eq_zero_of_lt X b q 0 τ hq, smul_zero, padFour_zero_right]

theorem faceRAt_front_pt (X : TopCat.{0}) (k a p q M'' B : ℕ)
    (ρ : singularSimplices X 0) (τ : singularSimplices X (M'' + 1)) (hp : 0 < p) :
    faceRAt X k a p q M'' ρ τ B = 0 := by
  rw [faceRAt_eq, phiAtDeg_eq_zero_of_lt X a p 0 ρ hp, padFour_zero_left]

theorem faceLAt_back_pt (X : TopCat.{0}) (k b p q M' A : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X 0) (hq : 0 < q) :
    faceLAt X k b p q M' ρ τ A = 0 := by
  rw [faceLAt_eq, phiAtDeg_eq_zero_of_lt X b q 0 τ hq, smul_zero, padFour_zero_right]

/-! ## The generator acts trivially on a point -/

/-- One surplus power of the generator on a cochain of a point is no power at
all. -/
theorem smul_succ_phiAtDeg_pt (X : TopCat.{0}) (p : ℕ) (τ : singularSimplices X 0) :
    (groupRingGen ^ (p + 1)) • phiAtDeg X 0 0 τ
      = (groupRingGen ^ p) • phiAtDeg X 0 0 τ := by
  rw [← smul_pow_swapEnd X 0 p (phiAtDeg X 0 0 τ), swapEnd_phiAtDeg_degree_zero]

/-! ## The front-degenerate branch -/

/-- **When the front simplex is a point.**  Only the summand at index `0`
survives, and its right block produces the level-`i` summand, the swap term, and
the faces of the back simplex. -/
theorem sum_tensorD_front_zero (X : TopCat.{0}) (k i M'' : ℕ)
    (ρ : singularSimplices X 0) (τ : singularSimplices X (M'' + 1)) :
    (∑ p ∈ Finset.range (i + 2),
        tensorD (pairFreeCx X) (pairFreeCx X) k
          (bTerm X (k + 1) (0 + p) (M'' + 1 + (i + 1 - p)) p (i + 1 - p) ρ τ))
      = ((∑ p ∈ Finset.range (i + 1),
              bTerm X k (0 + p) (M'' + 1 + (i - p)) p (i - p) ρ τ)
            + innerSwapFour X k
                (∑ p ∈ Finset.range (i + 1),
                  bTerm X k (0 + p) (M'' + 1 + (i - p)) p (i - p) ρ τ))
          + ∑ p ∈ Finset.range (i + 2),
              faceRAt X k (0 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p)) := by
  have hmem : (0 : ℕ) ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
  have hmem' : (0 : ℕ) ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem 0 hmem (fun b _ hb => by
        obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
        rw [bTerm_front_pt X (k + 1) _ _ (b' + 1) _ ρ τ (Nat.succ_pos b'), map_zero]),
    Finset.sum_eq_single_of_mem 0 hmem' (fun b _ hb => by
        obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
        exact bTerm_front_pt X k _ _ (b' + 1) _ ρ τ (Nat.succ_pos b')),
    Finset.sum_eq_single_of_mem 0 hmem (fun b _ hb => by
        obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
        exact faceRAt_front_pt X k _ (b' + 1) _ M'' _ ρ τ (Nat.succ_pos b'))]
  show tensorD (pairFreeCx X) (pairFreeCx X) k
        (bTerm X (k + 1) 0 (M'' + 1 + i + 1) 0 (i + 1) ρ τ)
      = (bTerm X k 0 (M'' + 1 + i) 0 i ρ τ
            + innerSwapFour X k (bTerm X k 0 (M'' + 1 + i) 0 i ρ τ))
          + faceRAt X k 0 0 (i + 1) M'' ρ τ (M'' + (i + 1))
  rw [tensorD_bTerm, padFourL_eq_zero_of_front rfl, zero_add,
    bTerm_right_split X k 0 M'' i 0 ρ τ, innerSwapFour_bTerm,
    swapEnd_phiAtDeg_degree_zero,
    faceRAt_congr X k 0 0 (i + 1) M'' ρ τ
      (show M'' + (i + 1) = M'' + 1 + i by omega),
    faceRAt_eq]

/-! ## The back-degenerate branch -/

/-- **When the back simplex is a point.**  Only the summand at index `i + 1`
survives, and its left block produces all three pieces; the level-`i` summand
appears with one power of the generator too many, which the triviality of the
action on a point removes. -/
theorem sum_tensorD_back_zero (X : TopCat.{0}) (k i M' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X 0) :
    (∑ p ∈ Finset.range (i + 2),
        tensorD (pairFreeCx X) (pairFreeCx X) k
          (bTerm X (k + 1) (M' + 1 + p) (0 + (i + 1 - p)) p (i + 1 - p) ρ τ))
      = ((∑ p ∈ Finset.range (i + 1),
              bTerm X k (M' + 1 + p) (0 + (i - p)) p (i - p) ρ τ)
            + innerSwapFour X k
                (∑ p ∈ Finset.range (i + 1),
                  bTerm X k (M' + 1 + p) (0 + (i - p)) p (i - p) ρ τ))
          + ∑ p ∈ Finset.range (i + 2),
              faceLAt X k (0 + (i + 1 - p)) p (i + 1 - p) M' ρ τ (M' + p) := by
  have hmem : (i + 1) ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
  have hmem' : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem (i + 1) hmem (fun b hb hne => by
        have hlt : 0 < i + 1 - b := by
          have := Finset.mem_range.mp hb
          omega
        rw [bTerm_back_pt X (k + 1) _ _ b (i + 1 - b) ρ τ hlt, map_zero]),
    Finset.sum_eq_single_of_mem i hmem' (fun b hb hne => by
        have hlt : 0 < i - b := by
          have := Finset.mem_range.mp hb
          omega
        exact bTerm_back_pt X k _ _ b (i - b) ρ τ hlt),
    Finset.sum_eq_single_of_mem (i + 1) hmem (fun b hb hne => by
        have hlt : 0 < i + 1 - b := by
          have := Finset.mem_range.mp hb
          omega
        exact faceLAt_back_pt X k _ b (i + 1 - b) M' _ ρ τ hlt)]
  rw [bTerm_back_congr X (k + 1) (M' + 1 + (i + 1)) (i + 1) ρ τ (Nat.sub_self (i + 1)),
    bTerm_back_congr X k (M' + 1 + i) i ρ τ (Nat.sub_self i),
    faceLAt_back_congr X k (i + 1) M' (M' + (i + 1)) ρ τ (Nat.sub_self (i + 1))]
  show tensorD (pairFreeCx X) (pairFreeCx X) k
        (bTerm X (k + 1) (M' + 1 + i + 1) 0 (i + 1) 0 ρ τ)
      = (bTerm X k (M' + 1 + i) 0 i 0 ρ τ
            + innerSwapFour X k (bTerm X k (M' + 1 + i) 0 i 0 ρ τ))
          + faceLAt X k 0 (i + 1) 0 M' ρ τ (M' + (i + 1))
  rw [tensorD_bTerm, padFourR_eq_zero_of_back rfl, add_zero,
    bTerm_left_split X k M' i 0 0 ρ τ, bTerm_eq,
    faceLAt_congr X k 0 (i + 1) 0 M' ρ τ
      (show M' + (i + 1) = M' + 1 + i by omega),
    faceLAt_eq, ← smul_succ_phiAtDeg_pt X i τ]

end

end Steenrod
end CharClass
end GroupApproximation
