import GroupApproximation.CharClass.LIXStepDGenRealEven
import GroupApproximation.Meta.AxiomGuard

/-!
# The reduced powers at an odd prime, as the Step D producers consume them

Two named structures, stated before anything produces them, so that the lanes that consume the
reduced powers (`Gen.RealTorusModP`, the splitting principle over `K`, `Gen.RealBundleModP`) and
the lanes that construct them (the equivariant diagonal, the classes `redPow`, additivity, the top
power and the `P⁰` constant, the Cartan formula) meet at one citable name each.

* `OddPTotal.EvenReducedPowers p` — the consumer-facing form.  For every space `X`, additive
  operations `P X i` on the even part `Gen.evenPart (ZMod p) X` (the commutative ring the even side
  of Step D lives in), natural along pullback, with `P⁰ = id`, the Cartan formula, the degree shift
  `d ↦ d + 2i(p − 1)`, instability, and `P¹ h = κ·h^p` on degree-two classes for an integer `κ`
  that is a unit mod `p`.
* `OddPTotal.GradedReducedPowers p` — the producer-facing form, one degree at a time and not
  normalised: operations `op X d i : H^d(X; F_p) → H^{d + 2i(p−1)}(X; F_p)`, natural, unstable,
  with `P⁰ = c^{d/2}·id` in even degrees for a unit `c`, the top power `P¹ h = h^p` in degree two,
  and the Cartan formula for two classes of even degree.

`OddPTotalPackaging.lean` turns the second into the first: normalise by `c^{-d/2}` in degree `d`
and assemble over the grading.

## Why only even degrees

Every class the even side touches is even: the Chern classes, the Chern roots, the slice
generators, and `z = t x`.  In even degrees the construction is sign-free.  Every `W`-index
`(d − 2i)(p − 1)` is even, the reduced coproduct coefficient at two even indices is `1`, the
odd–odd coefficient vanishes mod `p`, and the Koszul sign of two even classes is `+1`.  The
normalisation constant is multiplicative there too.  In odd degrees `P⁰ = c_q·id` with
`c_1 = ((p − 1)/2)!`, and the Cartan formula carries `(−1)^{qq'(p−1)/2}`; no consumer needs either.
The one product of two odd classes used so far, `t·x` in `Gen.RealTorusModP.PN_zClass`, is
replaced by `P^{>0} z = 0`.  That follows from naturality along the projection to
`S¹ × S^{2n+1}`, the degree shift, and the vanishing of the torus cohomology above its dimension.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

/-- A homogeneous class of even degree, as an element of the even part. -/
def evenOf (K : Type) [CommRing K] (X : TopCat.{0}) {d : ℕ} (hd : Even d)
    (c : TotalPieceOf K X d) : Gen.evenPart K X :=
  ⟨TotalHOf.of K X d c, TotalHOf.isEven_of K X hd c⟩

@[simp] theorem coe_evenOf (K : Type) [CommRing K] (X : TopCat.{0}) {d : ℕ} (hd : Even d)
    (c : TotalPieceOf K X d) : (evenOf K X hd c : TotalHOf K X) = TotalHOf.of K X d c :=
  rfl

/-- **The reduced powers on the even part of mod-`p` cohomology**, in the form the Step D
producers consume.

Consumers: `Gen.RealTorusModP` (`PN`, `PY`, `PN_zero`, `cartan`, `natural`, `PY_unstable`, and
`P^{>0} z = 0` through `shift`), the splitting principle over `K` (the `ParityP.PowerData` on the
flag space, with `κ` the integer of `hone`), and `Gen.RealBundleModP.wu`.  Producer:
`OddPTotal.GradedReducedPowers.toEven` (lane `lx-pzero`). -/
structure EvenReducedPowers (p : ℕ) where
  /-- The reduced power `P^i` on the even part of `H^*(X; F_p)`. -/
  P : ∀ (X : TopCat.{0}), ℕ → Gen.evenPart (ZMod p) X →+ Gen.evenPart (ZMod p) X
  /-- Naturality along pullback. -/
  natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (i : ℕ) (x : Gen.evenPart (ZMod p) Y),
    P X i (Gen.evenMap (ZMod p) f x) = Gen.evenMap (ZMod p) f (P Y i x)
  /-- `P⁰ = id`. -/
  zero : ∀ (X : TopCat.{0}) (x : Gen.evenPart (ZMod p) X), P X 0 x = x
  /-- The Cartan formula. -/
  cartan : ∀ (X : TopCat.{0}) (i : ℕ) (u v : Gen.evenPart (ZMod p) X),
    P X i (u * v) = ∑ j ∈ Finset.range (i + 1), P X j u * P X (i - j) v
  /-- `P^i` raises the degree by `2i(p − 1)`. -/
  shift : ∀ (X : TopCat.{0}) (i : ℕ) {d : ℕ} (hd : Even d) (c : TotalPieceOf (ZMod p) X d),
    ∃ c' : TotalPieceOf (ZMod p) X (d + 2 * i * (p - 1)),
      (P X i (evenOf (ZMod p) X hd c) : TotalHOf (ZMod p) X)
        = TotalHOf.of (ZMod p) X (d + 2 * i * (p - 1)) c'
  /-- Instability: `P^i` vanishes on classes of degree `< 2i`. -/
  unstable : ∀ (X : TopCat.{0}) (i : ℕ) {d : ℕ} (hd : Even d) (c : TotalPieceOf (ZMod p) X d),
    d < 2 * i → P X i (evenOf (ZMod p) X hd c) = 0
  /-- The normalisation constant of the degree-two relation, as an integer. -/
  κ : ℤ
  /-- The constant is a unit mod `p`. -/
  κ_isUnit : IsUnit (κ : ZMod p)
  /-- `P¹ h = κ·h^p` on classes of degree two. -/
  degree_two : ∀ (X : TopCat.{0}) (c : TotalPieceOf (ZMod p) X 2),
    P X 1 (evenOf (ZMod p) X even_two c)
      = (κ : Gen.evenPart (ZMod p) X) * evenOf (ZMod p) X even_two c ^ p

/-- **The reduced powers degree by degree, as the cochain construction delivers them**, before
normalisation and only consulted in even degrees where it matters.

Producers: the classes `op` with naturality and instability from `redPow` (R3, R6–R8) and additivity
(R9); `zero` and `top_two` from the top power and the `P⁰` constant; `cartan` from the comparison
of equivariant diagonals.  Consumer: `OddPTotal.GradedReducedPowers.toEven`. -/
structure GradedReducedPowers (p : ℕ) where
  /-- The reduced power `P^i : H^d(X; F_p) → H^{d + 2i(p−1)}(X; F_p)`. -/
  op : ∀ (X : TopCat.{0}) (d i : ℕ), Hmod (ZMod p) X d →+ Hmod (ZMod p) X (d + 2 * i * (p - 1))
  /-- Naturality along pullback. -/
  natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (d i : ℕ) (x : Hmod (ZMod p) Y d),
    pull f (d + 2 * i * (p - 1)) (op Y d i x) = op X d i (pull f d x)
  /-- Instability. -/
  unstable : ∀ (X : TopCat.{0}) (d i : ℕ) (x : Hmod (ZMod p) X d), d < 2 * i → op X d i x = 0
  /-- The `P⁰` constant in degree two. -/
  c : ZMod p
  /-- It is a unit. -/
  c_isUnit : IsUnit c
  /-- `P⁰ = c^{d/2}·id` in even degree `d`. -/
  zero : ∀ (X : TopCat.{0}) {d : ℕ} (_hd : Even d) (x : Hmod (ZMod p) X d),
    TotalHOf.of (ZMod p) X (d + 2 * 0 * (p - 1)) (op X d 0 x)
      = c ^ (d / 2) • TotalHOf.of (ZMod p) X d x
  /-- The top power in degree two: `P¹ h = h^p`. -/
  top_two : ∀ (X : TopCat.{0}) (x : Hmod (ZMod p) X 2),
    TotalHOf.of (ZMod p) X (2 + 2 * 1 * (p - 1)) (op X 2 1 x) = TotalHOf.of (ZMod p) X 2 x ^ p
  /-- The Cartan formula for two classes of even degree. -/
  cartan : ∀ (X : TopCat.{0}) {d d' : ℕ} (_hd : Even d) (_hd' : Even d') (k : ℕ)
      (x : Hmod (ZMod p) X d) (y : Hmod (ZMod p) X d'),
    TotalHOf.of (ZMod p) X (d + d' + 2 * k * (p - 1)) (op X (d + d') k (cup x y))
      = ∑ i ∈ Finset.range (k + 1),
          TotalHOf.of (ZMod p) X (d + 2 * i * (p - 1)) (op X d i x)
            * TotalHOf.of (ZMod p) X (d' + 2 * (k - i) * (p - 1)) (op X d' (k - i) y)

end

end OddPTotal

#audit_axioms OddPTotal.evenOf
#audit_axioms OddPTotal.coe_evenOf
#audit_axioms OddPTotal.EvenReducedPowers
#audit_axioms OddPTotal.GradedReducedPowers

end CharClass
end GroupApproximation
