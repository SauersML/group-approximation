import GroupApproximation.CharClass.OddPTotalPackaging
import GroupApproximation.CharClass.OddPAdditive

/-!
# The producer of `OddPTotal.TotalReducedPowers p` at an odd prime

The classes `[D_j]` of the equivariant construction (`oddDClass`, `CharClass/OddPRedPow.lean`) form
the family `oddDAdd p hp X q j : H^q(X; F_p) →+ H^{pq − j}(X; F_p)`.  It is additive at every index
by `oddD_class_add`, and zero above `pq`.  Naturality is `oddDClass_natural`.

The remaining fields of `TotalReducedPowers` are stated here as five named propositions about this
family, one per producing lane:
* `UnitZeroOddP`, `TopTwoOddP` — the top power (`lx-toppower`);
* `PtotMulOddP`, `BadTwoOddP` — the Cartan comparison and V (`lx-cartan-b`);
* `ZeroCPOddP μ` with `IsUnit μ` — the `P⁰` constant on `H²(ℂP^M)` (`lx-toppower`, `lx-design`).

`totalReducedPowersOddP` assembles the structure from them, and
`(totalReducedPowersOddP …).toEven hp2` is the operations interface the Step D producers consume.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

variable (p : ℕ) [Fact p.Prime] (hp : Odd p)

/-- The class of `D_j` is additive at every index. -/
theorem oddDClass_add (X : TopCat.{0}) (q j : ℕ) (hj : j ≤ p * q) (x y : Hmod (ZMod p) X q) :
    oddDClass p hp q j hj (x + y) = oddDClass p hp q j hj x + oddDClass p hp q j hj y := by
  obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective (ZMod p) X q x
  obtain ⟨v, hv, rfl⟩ := cocycleClassK_surjective (ZMod p) X q y
  have huv : cochainCoboundary (ZMod p) X q (u + v) = 0 := by
    rw [oddCochainCoboundary_add, hu, hv, add_zero]
  rw [← CupOneLocal.cocycleClassK_add (ZMod p) X q u v hu hv huv, oddDClass_mk, oddDClass_mk,
    oddDClass_mk, oddD_class_add p hp q j hj u v hu hv huv]

/-- **The family of classes `[D_j]`**, additive, and zero above `pq`. -/
def oddDAdd (X : TopCat.{0}) (q j : ℕ) : Hmod (ZMod p) X q →+ Hmod (ZMod p) X (p * q - j) :=
  if hj : j ≤ p * q then AddMonoidHom.mk' (oddDClass p hp q j hj) (oddDClass_add p hp X q j hj)
  else 0

theorem oddDAdd_apply (X : TopCat.{0}) (q j : ℕ) (hj : j ≤ p * q) (x : Hmod (ZMod p) X q) :
    oddDAdd p hp X q j x = oddDClass p hp q j hj x := by
  rw [oddDAdd, dif_pos hj]
  rfl

theorem oddDAdd_of_lt (X : TopCat.{0}) (q j : ℕ) (hj : p * q < j) (x : Hmod (ZMod p) X q) :
    oddDAdd p hp X q j x = 0 := by
  rw [oddDAdd, dif_neg (by omega)]
  rfl

theorem oddDAdd_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (q j : ℕ) (x : Hmod (ZMod p) Y q) :
    pull f (p * q - j) (oddDAdd p hp Y q j x) = oddDAdd p hp X q j (pull f q x) := by
  by_cases hj : j ≤ p * q
  · rw [oddDAdd_apply p hp Y q j hj, oddDAdd_apply p hp X q j hj, oddDClass_natural]
  · rw [oddDAdd_of_lt p hp Y q j (by omega), oddDAdd_of_lt p hp X q j (by omega), pull_zero]

/-- **`[D_0 1] = 1`**: the top power in degree zero.  Producer: `lx-toppower`. -/
def UnitZeroOddP : Prop :=
  ∀ X : TopCat.{0}, TotalHOf.of (ZMod p) X (p * 0 - 0) (oddDAdd p hp X 0 0 (one X)) = 1

/-- **The total power is multiplicative on classes of even degree.**  Producer: `lx-cartan-b`. -/
def PtotMulOddP : Prop :=
  ∀ (X : TopCat.{0}) {q q' : ℕ} (_hq : Even q) (_hq' : Even q')
    (x : Hmod (ZMod p) X q) (y : Hmod (ZMod p) X q'),
    ptotOf (oddDAdd p hp) X (q + q') (cup x y)
      = ptotOf (oddDAdd p hp) X q x * ptotOf (oddDAdd p hp) X q' y

/-- **The top power in degree two**, `[D_0 h] = h^p`.  Producer: `lx-toppower`. -/
def TopTwoOddP : Prop :=
  ∀ (X : TopCat.{0}) (h : Hmod (ZMod p) X 2),
    TotalHOf.of (ZMod p) X (p * 2 - 0) (oddDAdd p hp X 2 0 h) = TotalHOf.of (ZMod p) X 2 h ^ p

/-- **V in degree two**: only the indices `0` and `2(p − 1)` contribute.  Producer: `lx-cartan-b`. -/
def BadTwoOddP : Prop :=
  ∀ (X : TopCat.{0}) (h : Hmod (ZMod p) X 2) (j : ℕ), j % 2 = 0 → j ≠ 0 → j ≠ 2 * (p - 1) →
    oddDAdd p hp X 2 j h = 0

/-- **The `P⁰` constant on `H²(ℂP^M)`**: `[D_{2(p−1)} h] = μ·h`.  Producer: `lx-toppower`
(`IsUnit μ` through the T² corner of `lx-cartan-b` and the descent constant). -/
def ZeroCPOddP (μ : ZMod p) : Prop :=
  ∀ (M : ℕ) (h : Hmod (ZMod p) (CPtop M) 2),
    TotalHOf.of (ZMod p) (CPtop M) (p * 2 - 2 * (p - 1)) (oddDAdd p hp (CPtop M) 2 (2 * (p - 1)) h)
      = μ • TotalHOf.of (ZMod p) (CPtop M) 2 h

/-- **The reduced powers at an odd prime**, from the five named inputs. -/
def totalReducedPowersOddP (hunit : UnitZeroOddP p hp) (hmul : PtotMulOddP p hp)
    (htop : TopTwoOddP p hp) (hbad : BadTwoOddP p hp) (μ : ZMod p) (hμ : IsUnit μ)
    (hcp : ZeroCPOddP p hp μ) : TotalReducedPowers p where
  D := oddDAdd p hp
  natural f q j x := oddDAdd_natural p hp f q j x
  unit_zero := hunit
  ptot_mul := hmul
  top_two := htop
  bad_two := hbad
  μ := μ
  μ_isUnit := hμ
  zero_cp := hcp

/-- **The operations interface at an odd prime**, from the five named inputs. -/
def evenReducedPowersOddP (hunit : UnitZeroOddP p hp) (hmul : PtotMulOddP p hp)
    (htop : TopTwoOddP p hp) (hbad : BadTwoOddP p hp) (μ : ZMod p) (hμ : IsUnit μ)
    (hcp : ZeroCPOddP p hp μ) : EvenReducedPowers p :=
  (totalReducedPowersOddP p hp hunit hmul htop hbad μ hμ hcp).toEven (Fact.out : p.Prime).two_le

end

end OddPTotal

#audit_axioms OddPTotal.oddDClass_add
#audit_axioms OddPTotal.oddDAdd_natural
#audit_axioms OddPTotal.totalReducedPowersOddP
#audit_axioms OddPTotal.evenReducedPowersOddP

end CharClass
end GroupApproximation
