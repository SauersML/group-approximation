import GroupApproximation.CharClass.LIXStepDGenRealEven
import GroupApproximation.CharClass.ProjectiveSpaceCover
import GroupApproximation.Meta.AxiomGuard

/-!
# The reduced powers at an odd prime, as the Step D producers consume them

Two named structures, stated before anything produces them, so that the lanes that consume the
reduced powers and the lanes that construct them meet at one citable name each.

* `OddPTotal.TotalReducedPowers p` — the producer-facing form.  The classes
  `D X q j : H^q(X; F_p) → H^{pq − j}(X; F_p)` of the equivariant construction, natural in `X`,
  and the total power `ptotOf D X q x = Σ_{j even} [D_j x]`, multiplicative on classes of even
  degree.  Besides naturality and multiplicativity, the fields are:
  - `unit_zero`: `D_0` of the unit is the unit;
  - `top_two`: the top power in degree two, `[D_0 h] = h^p`;
  - `bad_two`: the vanishing of `[D_j h]` in degree two at the indices `j ∉ {0, 2(p − 1)}`;
  - `zero_cp`: the constant `μ` of `[D_{2(p−1)}]` on `H²(ℂP^M)`, a unit.
* `OddPTotal.EvenReducedPowers p` — the consumer-facing form.
  - Graded operations `P X i` on the even part `Gen.evenPart (ZMod p) X`, normalised by
    `μ^{-(k − i)}` in degree `2k`.  They are natural for all classes, with the degree shift and
    instability.
  - The ring endomorphism `Ptot X` and the subring `Good X` of junk-free classes, on which the
    Cartan formula holds.  `Good X` contains every degree-two class and is natural.
  - `mul_single`: `P^i` passes through a class whose total power is a multiple of itself.
  - `P⁰ 1 = 1`, `P⁰ = id` on `H²(ℂP^M)`, and `P¹ h = h^p` in degree two.

`OddPTotalPackaging.lean` proves `TotalReducedPowers p → EvenReducedPowers p`.

## What is not here, and why

There is no `P⁰ = id` on arbitrary classes and no Cartan formula for arbitrary classes.  `P⁰` on
all of `H^q` is a universal-example statement (`K(ℤ/p, q)`), which singular chains built by
acyclic models do not give.  The graded Cartan formula on arbitrary even classes needs the
vanishing of above-range classes `[D_a x]`, `a > q(p − 1)`, which has no cheap singular-chain
proof.  Neither is consumed:

* on the flag space the operations meet only 1, the Chern roots (Euler classes of line bundles,
  pulled back from `H²(ℂP^M)`) and products of roots, all in `Good`;
* on the mapping torus the class `z = t x` has a single-component total power (its target
  degrees on `S¹ × S^{2n+1}` are `0` and `2n + 2`), so `mul_single` gives
  `P^i(z·ι r) = c·z·ι(P^i r)` for every even class `r`.
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

/-- The degrees in which the reduced powers of a class of degree `d` live: `d + 2s(p − 1)`. -/
def GoodDeg (p d e : ℕ) : Prop := d ≤ e ∧ (e - d) % (2 * (p - 1)) = 0

instance (p d e : ℕ) : Decidable (GoodDeg p d e) := by
  unfold GoodDeg; infer_instance

/-- **The total reduced power** of a class of degree `q`, from the family of classes
`[D_j] : H^q → H^{pq − j}`: the sum of `[D_j x]` over the even indices `j ≤ pq`. -/
def ptotOf {p : ℕ}
    (D : ∀ (X : TopCat.{0}) (q j : ℕ), Hmod (ZMod p) X q →+ Hmod (ZMod p) X (p * q - j))
    (X : TopCat.{0}) (q : ℕ) : Hmod (ZMod p) X q →+ TotalHOf (ZMod p) X :=
  ∑ j ∈ Finset.range (p * q + 1),
    if j % 2 = 0 then (TotalHOf.of (ZMod p) X (p * q - j)).comp (D X q j) else 0

/-- **The reduced powers as the equivariant construction delivers them.**

Producers:
* `D`, `natural`: the classes `[D_j]` (`lx-redpow`), additive by R9 (`lx-additive`);
* `ptot_mul`: the comparison of equivariant diagonals (`lx-cartan-b`);
* `unit_zero`, `top_two`: the top power (`lx-toppower`);
* `bad_two`: V in degree two (`lx-cartan-b`);
* `μ`, `zero_cp`: the `P⁰` constant on `H²(ℂP^M)` and its unit property (`lx-toppower`,
  `lx-design`).

Consumer: `OddPTotal.TotalReducedPowers.toEven`. -/
structure TotalReducedPowers (p : ℕ) where
  /-- The class `[D_j x] ∈ H^{pq − j}(X; F_p)` of a class `x ∈ H^q(X; F_p)`. -/
  D : ∀ (X : TopCat.{0}) (q j : ℕ), Hmod (ZMod p) X q →+ Hmod (ZMod p) X (p * q - j)
  /-- Naturality along pullback. -/
  natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (q j : ℕ) (x : Hmod (ZMod p) Y q),
    pull f (p * q - j) (D Y q j x) = D X q j (pull f q x)
  /-- `[D_0 1] = 1`. -/
  unit_zero : ∀ X : TopCat.{0},
    TotalHOf.of (ZMod p) X (p * 0 - 0) (D X 0 0 (one X)) = 1
  /-- The total power is multiplicative on classes of even degree. -/
  ptot_mul : ∀ (X : TopCat.{0}) {q q' : ℕ} (_hq : Even q) (_hq' : Even q')
      (x : Hmod (ZMod p) X q) (y : Hmod (ZMod p) X q'),
    ptotOf D X (q + q') (cup x y) = ptotOf D X q x * ptotOf D X q' y
  /-- The top power in degree two: `[D_0 h] = h^p`. -/
  top_two : ∀ (X : TopCat.{0}) (h : Hmod (ZMod p) X 2),
    TotalHOf.of (ZMod p) X (p * 2 - 0) (D X 2 0 h) = TotalHOf.of (ZMod p) X 2 h ^ p
  /-- In degree two only the indices `0` and `2(p − 1)` contribute. -/
  bad_two : ∀ (X : TopCat.{0}) (h : Hmod (ZMod p) X 2) (j : ℕ), j % 2 = 0 → j ≠ 0 →
    j ≠ 2 * (p - 1) → D X 2 j h = 0
  /-- The `P⁰` constant in degree two. -/
  μ : ZMod p
  /-- It is a unit. -/
  μ_isUnit : IsUnit μ
  /-- `[D_{2(p−1)} h] = μ·h` on `H²(ℂP^M)`. -/
  zero_cp : ∀ (M : ℕ) (h : Hmod (ZMod p) (CPtop M) 2),
    TotalHOf.of (ZMod p) (CPtop M) (p * 2 - 2 * (p - 1)) (D (CPtop M) 2 (2 * (p - 1)) h)
      = μ • TotalHOf.of (ZMod p) (CPtop M) 2 h

/-- **The reduced powers on the even part of mod-`p` cohomology**, in the form the Step D
producers consume.

Consumers:
* the flag space (`lx-splitK`): the roots are Euler classes, hence in `Good` (`good_two`), and
  their products are in `Good` because it is a subring.  So `cartan`, `zero_one` and `zero_cp`
  with naturality give the narrowed `PowerData`, with `degree_two` (`κ = 1`) and `unstable`.
* the mapping torus (`lx-torusP`, `lx-slice2`): `natural`, `shift`, `unstable`, and `mul_single`
  for `z = t x`.

Producer: `OddPTotal.TotalReducedPowers.toEven` (lane `lx-pzero`). -/
structure EvenReducedPowers (p : ℕ) where
  /-- The reduced power `P^i` on the even part of `H^*(X; F_p)`. -/
  P : ∀ (X : TopCat.{0}), ℕ → Gen.evenPart (ZMod p) X →+ Gen.evenPart (ZMod p) X
  /-- Naturality along pullback. -/
  natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (i : ℕ) (x : Gen.evenPart (ZMod p) Y),
    P X i (Gen.evenMap (ZMod p) f x) = Gen.evenMap (ZMod p) f (P Y i x)
  /-- `P^i` raises the degree by `2i(p − 1)`. -/
  shift : ∀ (X : TopCat.{0}) (i : ℕ) {d : ℕ} (hd : Even d) (c : TotalPieceOf (ZMod p) X d),
    ∃ c' : TotalPieceOf (ZMod p) X (d + 2 * i * (p - 1)),
      (P X i (evenOf (ZMod p) X hd c) : TotalHOf (ZMod p) X)
        = TotalHOf.of (ZMod p) X (d + 2 * i * (p - 1)) c'
  /-- Instability: `P^i` vanishes on classes of degree `< 2i`. -/
  unstable : ∀ (X : TopCat.{0}) (i : ℕ) {d : ℕ} (hd : Even d) (c : TotalPieceOf (ZMod p) X d),
    d < 2 * i → P X i (evenOf (ZMod p) X hd c) = 0
  /-- The total power, unnormalised, as a ring endomorphism of the even part. -/
  Ptot : ∀ X : TopCat.{0}, Gen.evenPart (ZMod p) X →+* Gen.evenPart (ZMod p) X
  /-- Naturality of the total power. -/
  ptot_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (x : Gen.evenPart (ZMod p) Y),
    Ptot X (Gen.evenMap (ZMod p) f x) = Gen.evenMap (ZMod p) f (Ptot Y x)
  /-- The junk-free classes, on which the Cartan formula holds. -/
  Good : ∀ X : TopCat.{0}, Subring (Gen.evenPart (ZMod p) X)
  /-- Pullbacks of junk-free classes are junk-free. -/
  good_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (x : Gen.evenPart (ZMod p) Y),
    x ∈ Good Y → Gen.evenMap (ZMod p) f x ∈ Good X
  /-- Every class of degree two is junk-free. -/
  good_two : ∀ (X : TopCat.{0}) (c : TotalPieceOf (ZMod p) X 2),
    evenOf (ZMod p) X even_two c ∈ Good X
  /-- A homogeneous class whose total power vanishes outside the degrees `d + 2s(p − 1)` is
  junk-free. -/
  good_of_components : ∀ (X : TopCat.{0}) {d : ℕ} (hd : Even d) (c : TotalPieceOf (ZMod p) X d),
    (∀ e : ℕ, e % 2 = 0 → ¬ GoodDeg p d e →
      TotalHOf.component (ZMod p) X e (Ptot X (evenOf (ZMod p) X hd c) : TotalHOf (ZMod p) X)
        = 0) →
    evenOf (ZMod p) X hd c ∈ Good X
  /-- The Cartan formula on junk-free classes. -/
  cartan : ∀ (X : TopCat.{0}) (i : ℕ) (u v : Gen.evenPart (ZMod p) X), u ∈ Good X → v ∈ Good X →
    P X i (u * v) = ∑ j ∈ Finset.range (i + 1), P X j u * P X (i - j) v
  /-- `P^i` passes through a homogeneous class whose total power is a multiple of itself. -/
  mul_single : ∀ (X : TopCat.{0}) {q : ℕ} (hq : Even q) (z : TotalPieceOf (ZMod p) X q)
      (ν : ZMod p),
    (Ptot X (evenOf (ZMod p) X hq z) : TotalHOf (ZMod p) X) = ν • TotalHOf.of (ZMod p) X q z →
    ∃ c : ZMod p, ∀ (i : ℕ) (w : Gen.evenPart (ZMod p) X),
      (P X i (evenOf (ZMod p) X hq z * w) : TotalHOf (ZMod p) X)
        = c • (TotalHOf.of (ZMod p) X q z * (P X i w : TotalHOf (ZMod p) X))
  /-- `P⁰ 1 = 1`. -/
  zero_one : ∀ X : TopCat.{0}, P X 0 1 = 1
  /-- `P⁰ = id` on `H²(ℂP^M)`; with `natural`, on every Euler class of a line bundle. -/
  zero_cp : ∀ (M : ℕ) (c : TotalPieceOf (ZMod p) (CPtop M) 2),
    P (CPtop M) 0 (evenOf (ZMod p) (CPtop M) even_two c) = evenOf (ZMod p) (CPtop M) even_two c
  /-- `P¹ h = h^p` in degree two. -/
  degree_two : ∀ (X : TopCat.{0}) (c : TotalPieceOf (ZMod p) X 2),
    P X 1 (evenOf (ZMod p) X even_two c) = evenOf (ZMod p) X even_two c ^ p

end

end OddPTotal

#audit_axioms OddPTotal.evenOf
#audit_axioms OddPTotal.coe_evenOf
#audit_axioms OddPTotal.GoodDeg
#audit_axioms OddPTotal.ptotOf
#audit_axioms OddPTotal.TotalReducedPowers
#audit_axioms OddPTotal.EvenReducedPowers

end CharClass
end GroupApproximation
