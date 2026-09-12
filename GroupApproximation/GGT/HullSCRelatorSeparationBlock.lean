import GroupApproximation.GGT.HullSCRelatorSeparationGaps

/-!
# Blocks of Hull's relator cannot be shifted, and where the geometry enters

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii and after Osin,
*Acylindrically hyperbolic groups*, Lemma 4.2.

Olshanskii's separation begins by matching the `H`-blocks of the two words one
to one.  The step that does it is this: if a block `h^{m_i}` of the relator is
carried onto a block `h^{m_j}` by elements of the base of length at most `eps`
on either side, then `i = j`.  This module proves that step, from one geometric
input and the exponent design of `GGT/HullSCRelatorSeparationGaps.lean`.

## The one geometric input

`x · h^{m_i} · x' = h^{m_j}` with `|x|_X, |x'|_X ≤ eps` is a quadrilateral in
`Γ(G, X ⊔ H)`: two sides are paths of at most `eps` base letters, hence
`(1, eps)`-quasi-geodesics, and two sides are single `H`-edges, hence geodesics.
Osin's Lemma 4.2 -- his simplified form of Dahmani--Guirardel--Osin's
Proposition 4.13, recorded in this repository as
`GGT.OsinComponents.IsolatedComponentBound` -- bounds `d̂` of an *isolated*
component of such a polygon by `C · 4`.  A deep block escapes the ball of radius
`rho`, so at `rho ≥ 4C(eps)` its component is not isolated; the only other
`H`-component of the quadrilateral is the block `h^{m_j}`, so the two are
connected, which says that their initial vertices lie in one left coset of `H`,
which says `x ∈ H`, and then `x' = h^{-m_i} x⁻¹ h^{m_j} ∈ H` as well.

That conclusion is the hypothesis `hgeo` below, and it is the only thing here
that is not proved: nothing in this repository instantiates
`GGT.OsinComponents.IsQuasiGeodesicPolygon`, so the polygon theory is not
available to prove it.  It is carried as an explicit binder rather than named,
and every consequence of it is a theorem.

## What the input buys, once the exponents are designed

`hgeo` places `x` and `x'` in `H`.  They are short in the *base*, and
`HullSC.mem_relBall_of_wordNorm_le` turns that into shortness in the *relative*
metric, so `x, x'` lie in the relative ball of radius `eps`, which is finite.
The exponents were chosen so that no two distinct ones are joined by elements of
that ball on either side (`HullSC.exists_separated_relator_exponents`), so
`i = j`.

The two halves are complementary and neither is redundant: without `hgeo` the
elements `x, x'` are short only in the base and the finiteness of the relative
ball says nothing about them; without the exponent design the geometry gives
`x, x' ∈ H` and stops.

## What remains of Olshanskii's separation

Block rigidity is the first of three steps.  What is still open is the passage
from it to the conclusion `listVal w' = y · listVal w · y⁻¹`: that a matched
prefix longer than `B` contains a block on each side, that the one-to-one
alignment of blocks propagates to a single rotation offset shared by the whole
prefix, and that a shared offset between two *different* members of the
symmetrized closure forces the global translation.  The last of these is where
`w' ≠ w` is spent.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Block

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **A block determines its exponent.**  The `H`-letters of Hull's relator are
powers of a loxodromic element, and a loxodromic element has infinite order, so
two letters agree only if their exponents do. -/
theorem exponent_eq_of_comp_eq (E : HypEmbeddedCore A N) {m m' : ℕ}
    (h : (GGT.RelLetter.comp () (E.lox ^ m) : GGT.RelLetter G Unit)
      = GGT.RelLetter.comp () (E.lox ^ m')) : m = m' := by
  injection h with _hlam hval
  exact injective_pow_of_not_isOfFinOrder
    (not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic) hval

/-- **Matched blocks carry equal exponents.**

If a block `h^i` of the relator is carried onto a block `h^j` by base words of
length at most `eps` on either side, then `i = j`.

The geometric input places the two conjugators in `H`
(`hgeo`); `HullSC.mem_relBall_of_wordNorm_le` then places them in the relative
ball of radius `eps`, whose finiteness is what the exponents were designed
against. -/
theorem exponent_eq_of_blockMatch (E : HypEmbeddedCore A N) {eps rho : ℕ}
    {ms : List ℕ}
    (hgeo : ∀ (i j : ℕ) (x x' : G), wordNorm E.rel.base x ≤ eps →
      wordNorm E.rel.base x' ≤ eps → E.lox ^ i ∉ E.rel.relBall () rho →
        E.lox ^ j ∉ E.rel.relBall () rho → x * E.lox ^ i * x' = E.lox ^ j →
          x ∈ E.rel.fam () ∧ x' ∈ E.rel.fam ())
    (hdeep : ∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ x ∈ E.rel.relBall () eps,
      ∀ x' ∈ E.rel.relBall () eps,
        x * E.lox ^ i * x' ≠ E.lox ^ j ∧ x * E.lox ^ i * x' ≠ (E.lox ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : wordNorm E.rel.base x ≤ eps) (hx' : wordNorm E.rel.base x' ≤ eps)
    (heq : x * E.lox ^ i * x' = E.lox ^ j) : i = j := by
  by_contra hij
  obtain ⟨hxf, hx'f⟩ := hgeo i j x x' hx hx' (hdeep i hi) (hdeep j hj) heq
  have hbase := isSymmetricGeneratingSet_base E
  exact (hsep i hi j hj hij x (mem_relBall_of_wordNorm_le hbase hxf hx) x'
    (mem_relBall_of_wordNorm_le hbase hx'f hx')).1 heq

/-- **Mirrored blocks carry equal exponents.**

A prefix matched between the relator and its *formal inverse* aligns `h^{m_i}`
against `(h^{m_j})⁻¹`, so the equation is `x · h^i · x' = (h^j)⁻¹`.  The same two
ingredients close it: the mirrored geometric input places the conjugators in
`H`, and the exponent design forbids the mirrored match at distinct exponents.

At `i = j` the mirrored match is *not* forbidden, and must not be: it is the
configuration in which the conclusion of Olshanskii's separation is a genuine
global translation -- `t` inverting the loxodromic, `w` the relator and `w'` its
formal inverse -- so forbidding it would forbid the true case.  The design
therefore separates exactly the distinct exponents, which is also the only
separation the greedy count can reach: at `i = j` the exponent occurs on both
sides of the equation and the forbidden set is not a fixed finite set. -/
theorem exponent_eq_of_mirroredBlockMatch (E : HypEmbeddedCore A N) {eps rho : ℕ}
    {ms : List ℕ}
    (hgeoInv : ∀ (i j : ℕ) (x x' : G), wordNorm E.rel.base x ≤ eps →
      wordNorm E.rel.base x' ≤ eps → E.lox ^ i ∉ E.rel.relBall () rho →
        (E.lox ^ j)⁻¹ ∉ E.rel.relBall () rho →
          x * E.lox ^ i * x' = (E.lox ^ j)⁻¹ →
            x ∈ E.rel.fam () ∧ x' ∈ E.rel.fam ())
    (hdeep : ∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
      (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ x ∈ E.rel.relBall () eps,
      ∀ x' ∈ E.rel.relBall () eps,
        x * E.lox ^ i * x' ≠ E.lox ^ j ∧ x * E.lox ^ i * x' ≠ (E.lox ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : wordNorm E.rel.base x ≤ eps) (hx' : wordNorm E.rel.base x' ≤ eps)
    (heq : x * E.lox ^ i * x' = (E.lox ^ j)⁻¹) : i = j := by
  by_contra hij
  obtain ⟨hxf, hx'f⟩ :=
    hgeoInv i j x x' hx hx' (hdeep i hi).1 (hdeep j hj).2 heq
  have hbase := isSymmetricGeneratingSet_base E
  exact (hsep i hi j hj hij x (mem_relBall_of_wordNorm_le hbase hxf hx) x'
    (mem_relBall_of_wordNorm_le hbase hx'f hx')).2 heq

/-- **Hull's relator can be given rigid blocks, at every length.**

Combining the exponent design with the geometric input: for every length there
are at least that many exponents, without repetition, all deep, and such that an
`eps`-match between any two of the corresponding blocks forces the two exponents
to be equal.

This is the form Olshanskii's argument consumes, and it is unconditional except
for `hgeo`. -/
theorem exists_blockRigid_exponents (E : HypEmbeddedCore A N) {eps rho : ℕ}
    (hgeo : ∀ (i j : ℕ) (x x' : G), wordNorm E.rel.base x ≤ eps →
      wordNorm E.rel.base x' ≤ eps → E.lox ^ i ∉ E.rel.relBall () rho →
        E.lox ^ j ∉ E.rel.relBall () rho → x * E.lox ^ i * x' = E.lox ^ j →
          x ∈ E.rel.fam () ∧ x' ∈ E.rel.fam ())
    (L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
        (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, ∀ x x' : G, wordNorm E.rel.base x ≤ eps →
        wordNorm E.rel.base x' ≤ eps → x * E.lox ^ i * x' = E.lox ^ j → i = j := by
  obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ :=
    exists_separated_relator_exponents E rho eps L
  refine ⟨ms, hlen, hnodup, hdeep, ?_⟩
  intro i hi j hj x x' hx hx' heq
  exact exponent_eq_of_blockMatch E hgeo (fun m hm => (hdeep m hm).1) hsep hi hj
    hx hx' heq

/-- **Hull's relator can be given blocks rigid in both directions, at every
length.**

The direct clause is the one a match between two rotations of the relator
consumes; the mirrored clause is the one a match between a rotation of the
relator and a rotation of its formal inverse consumes.  Both come from the same
exponent design, and neither costs anything beyond it. -/
theorem exists_mirrorRigid_exponents (E : HypEmbeddedCore A N) {eps rho : ℕ}
    (hgeo : ∀ (i j : ℕ) (x x' : G), wordNorm E.rel.base x ≤ eps →
      wordNorm E.rel.base x' ≤ eps → E.lox ^ i ∉ E.rel.relBall () rho →
        E.lox ^ j ∉ E.rel.relBall () rho → x * E.lox ^ i * x' = E.lox ^ j →
          x ∈ E.rel.fam () ∧ x' ∈ E.rel.fam ())
    (hgeoInv : ∀ (i j : ℕ) (x x' : G), wordNorm E.rel.base x ≤ eps →
      wordNorm E.rel.base x' ≤ eps → E.lox ^ i ∉ E.rel.relBall () rho →
        (E.lox ^ j)⁻¹ ∉ E.rel.relBall () rho →
          x * E.lox ^ i * x' = (E.lox ^ j)⁻¹ →
            x ∈ E.rel.fam () ∧ x' ∈ E.rel.fam ())
    (L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
        (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, ∀ x x' : G, wordNorm E.rel.base x ≤ eps →
        wordNorm E.rel.base x' ≤ eps → x * E.lox ^ i * x' = E.lox ^ j → i = j) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, ∀ x x' : G, wordNorm E.rel.base x ≤ eps →
        wordNorm E.rel.base x' ≤ eps →
          x * E.lox ^ i * x' = (E.lox ^ j)⁻¹ → i = j) := by
  obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ :=
    exists_separated_relator_exponents E rho eps L
  refine ⟨ms, hlen, hnodup, hdeep, ?_, ?_⟩
  · intro i hi j hj x x' hx hx' heq
    exact exponent_eq_of_blockMatch E hgeo (fun m hm => (hdeep m hm).1) hsep hi hj
      hx hx' heq
  · intro i hi j hj x x' hx hx' heq
    exact exponent_eq_of_mirroredBlockMatch E hgeoInv hdeep hsep hi hj hx hx' heq

/-- **Depth at the radius the geometry needs is depth at the radius the
condition asks for.**

`hgeo` fixes its own radius, larger than the one `C(eps, mu, rho)` names.  The
relator is chosen deep at the larger radius, and `HullSC.notMem_relBall_of_le`
carries the depth clause back down to `rho`, so raising the radius costs the
estimate nothing. -/
theorem blockRigid_exponents_deep_of_le (E : HypEmbeddedCore A N) {rho rho' : ℕ}
    (hle : rho ≤ rho') {ms : List ℕ}
    (hdeep : ∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho' ∧
      (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho') :
    ∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
      (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho := by
  intro m hm
  exact ⟨notMem_relBall_of_le hle (hdeep m hm).1,
    notMem_relBall_of_le hle (hdeep m hm).2⟩

end Block

end HullSC
end GroupApproximation
