import GroupApproximation.CharClass.OddPCochain
import GroupApproximation.CharClass.OddPClasses

/-!
# The reduced powers `P^i` at an odd prime, on cohomology

For a cocycle `u ∈ C^q(X; F_p)` the cochain operation `D_j(u) ∈ C^{pq−j}(X; F_p)` of
`OddPCochain.lean` is natural and carries cocycles to cocycles (`oddD_natural`, `oddD_cocycle`).
`OddPClasses.lean` turns any such operation into a natural map on cohomology.  The reduced power
`P^i : H^q → H^{q + 2i(p−1)}` is the one at index `j = (q − 2i)(p − 1)`, and it is `0` when
`2i > q`.

* `oddDOp` — `D_j` as a `NaturalCocycleOp`.
* `oddDClass` — its class map at every index `j ≤ pq`, with `oddDClass_mk` and `oddDClass_natural`.
* `redPow_deg`, `redPow_index_le` — the degree identity and the index bound.
* `redPow` — the reduced power; `redPow_eq_zero_of_lt` — instability below degree `2i`.
* `redPow_mk` — the value on the class of any cocycle representative.
* `redPow_natural` — naturality.

What this file does not prove: additivity (`OddPAdditive.lean`), the Cartan formula, the value of
`P^0`, or the top power `P^{q/2}(x) = x^p`.  None of them is needed to define `P^i`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

/-- A prime is nonzero, as the instance `oddD` asks for.  Local, so that the reduced powers need only
`[Fact p.Prime]` whatever instance path the pin provides. -/
theorem oddPRedPow_neZero (p : ℕ) [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] oddPRedPow_neZero

/-- **`D_j` as a natural cocycle operation**, at every index `j ≤ pq`. -/
def oddDOp (p : ℕ) [Fact p.Prime] (hp : Odd p) (q j : ℕ) (hj : j ≤ p * q) :
    NaturalCocycleOp (ZMod p) q (p * q - j) where
  op _ u := oddD p q j u
  natural f u := oddD_natural p f q j u
  cocycle _ u hu := oddD_cocycle p hp q j hj u hu

/-- **The class of `D_j`** at any index `j ≤ pq`: `H^q(X; F_p) → H^{pq−j}(X; F_p)`, the class of
`D_j` of a cocycle representative.  Every reduced power is one of these (`redPow`), and the
vanishing and Cartan statements are about all of them. -/
def oddDClass (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ) (hj : j ≤ p * q)
    (x : Hmod (ZMod p) X q) : Hmod (ZMod p) X (p * q - j) :=
  (oddDOp p hp q j hj).classMap X x

/-- **The computation rule for `oddDClass`**: on the class of any cocycle it is the class of
`D_j` of that cocycle. -/
theorem oddDClass_mk (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ)
    (hj : j ≤ p * q) (u : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) :
    oddDClass p hp q j hj (cocycleClassK (ZMod p) X q u hu)
      = cocycleClassK (ZMod p) X (p * q - j) (oddD p q j u) (oddD_cocycle p hp q j hj u hu) :=
  NaturalCocycleOp.classMap_mk (oddDOp p hp q j hj) X u hu

/-- **Naturality of `oddDClass`.** -/
theorem oddDClass_natural (p : ℕ) [Fact p.Prime] (hp : Odd p) {X Y : TopCat.{0}} (f : X ⟶ Y)
    (q j : ℕ) (hj : j ≤ p * q) (x : Hmod (ZMod p) Y q) :
    pull f (p * q - j) (oddDClass p hp q j hj x) = oddDClass p hp q j hj (pull f q x) :=
  NaturalCocycleOp.classMap_natural (oddDOp p hp q j hj) f x

/-- The index of `P^i` in degree `q` is at most `pq`. -/
theorem redPow_index_le (p q i : ℕ) : (q - 2 * i) * (p - 1) ≤ p * q :=
  calc (q - 2 * i) * (p - 1) ≤ q * p := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ = p * q := Nat.mul_comm q p

/-- **The degree of `P^i`**: `pq − (q − 2i)(p − 1) = q + 2i(p − 1)` when `2i ≤ q`. -/
theorem redPow_deg (p : ℕ) [Fact p.Prime] (q i : ℕ) (h : 2 * i ≤ q) :
    p * q - (q - 2 * i) * (p - 1) = q + 2 * i * (p - 1) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  obtain ⟨r, hr⟩ : ∃ r, q = 2 * i + r := ⟨q - 2 * i, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have e1 : q - 2 * i = r := by omega
  have e2 : p - 1 = s := by omega
  rw [e1, e2, hr, hs]
  have e3 : (s + 1) * (2 * i + r) = r * s + (2 * i + r + 2 * i * s) := by ring
  rw [e3, Nat.add_sub_cancel_left]

/-- **The reduced power** `P^i : H^q(X; F_p) → H^{q + 2i(p−1)}(X; F_p)` at an odd prime `p`:
the class of `D_{(q−2i)(p−1)}` of a cocycle representative, and `0` when `2i > q`. -/
def redPow (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (x : Hmod (ZMod p) X q) : Hmod (ZMod p) X (q + 2 * i * (p - 1)) :=
  if h : 2 * i ≤ q then
    cohCast (redPow_deg p q i h)
      ((oddDOp p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i)).classMap X x)
  else 0

/-- **Instability**: `P^i` vanishes on classes of degree below `2i`. -/
theorem redPow_eq_zero_of_lt (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (h : q < 2 * i) (x : Hmod (ZMod p) X q) : redPow p hp q i x = 0 :=
  dif_neg (by omega)

/-- **The computation rule**: on the class of any cocycle, `P^i` is the class of `D_j` of that
cocycle. -/
theorem redPow_mk (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ) (h : 2 * i ≤ q)
    (u : singularCochainGroup (ZMod p) X q) (hu : cochainCoboundary (ZMod p) X q u = 0) :
    redPow p hp q i (cocycleClassK (ZMod p) X q u hu)
      = cohCast (redPow_deg p q i h)
          (cocycleClassK (ZMod p) X (p * q - (q - 2 * i) * (p - 1))
            (oddD p q ((q - 2 * i) * (p - 1)) u)
            (oddD_cocycle p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i) u hu)) := by
  rw [redPow, dif_pos h]
  exact congrArg (cohCast (redPow_deg p q i h))
    (NaturalCocycleOp.classMap_mk (oddDOp p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i))
      X u hu)

/-- Pullback commutes with a degree cast. -/
theorem pull_cohCast_redPow {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) {m m' : ℕ}
    (h : m = m') (a : Hmod K Y m) : pull f m' (cohCast h a) = cohCast h (pull f m a) := by
  subst h
  rfl

/-- **Naturality of the reduced powers.** -/
theorem redPow_natural (p : ℕ) [Fact p.Prime] (hp : Odd p) {X Y : TopCat.{0}} (f : X ⟶ Y)
    (q i : ℕ) (x : Hmod (ZMod p) Y q) :
    pull f (q + 2 * i * (p - 1)) (redPow p hp q i x) = redPow p hp q i (pull f q x) := by
  by_cases h : 2 * i ≤ q
  · rw [redPow, dif_pos h, redPow, dif_pos h, pull_cohCast_redPow,
      NaturalCocycleOp.classMap_natural]
  · rw [redPow, dif_neg h, redPow, dif_neg h, pull_zero]

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms oddDClass_mk
#audit_axioms oddDClass_natural
#audit_axioms redPow_deg
#audit_axioms redPow
#audit_axioms redPow_eq_zero_of_lt
#audit_axioms redPow_mk
#audit_axioms redPow_natural
