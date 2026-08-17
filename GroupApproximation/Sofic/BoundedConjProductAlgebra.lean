import GroupApproximation.Sofic.SoficEnvelopeSimplicity

/-!
# The algebra of bounded products of conjugates

`Sofic/SoficEnvelopeSimplicity.lean` isolates the one external input of the
Elek--Szabó envelope theorem (proof-ledger row `SO.17`) as the premise `hBNG`,
**bounded normal generation of finite alternating groups**:

> for every `δ > 0` there are `K` and `M` such that whenever `Ω` is a finite
> set with `|Ω| ≥ M` and `s` is an even permutation of `Ω` with
> `|supp s| ≥ δ|Ω|`, every even permutation of `Ω` is a product of at most `K`
> conjugates of `s` and `s⁻¹`.

That premise is written with the structural predicate `IsBoundedConjProduct`,
which is inhabited outright and is proved there to refine normal generation.
What that file does *not* develop is the elementary algebra of the predicate:
that bounded conjugate products compose, are closed under conjugation, are
carried by homomorphisms, and that a commutator with `s` is one of length two.

This file supplies exactly that, unconditionally and in an arbitrary group.
Every declaration below is a complete theorem; nothing here is a hypothesis
in disguise, and in particular **nothing here proves or assumes `hBNG`**,
which remains the one open input of `SO.17`.

## Why these lemmas, and what is still missing

The elementary route to `hBNG` — the one that does not quote Liebeck--Shalev —
factors through two statements, and the API below is what both of them
consume.

1. *Production.*  For `s` even with `|supp s| = m`, and any `g`, the
   commutator `⁅s, g⁆` is a product of two conjugates of `s^{±1}`
   (`isBoundedConjProduct_commutator` below, which is the whole of this
   direction and is proved here).  Choosing `g` to be a product of `j`
   disjoint transpositions `(x_i y_i)` with `x_i ∈ supp s` and
   `y_i ∉ supp s`, and with the triples `{x_i, s⁻¹x_i, y_i}` pairwise
   disjoint, makes `⁅s, g⁆` a product of `j` disjoint `3`-cycles; conjugating
   the result (`isBoundedConjProduct_conj`) then reaches *every* element of
   that cycle type.  The combinatorial input is the extraction of `j ≈ m/3`
   such triples from the support of `s`, which is not formalized anywhere in
   this repository.
2. *Consumption.*  Every even permutation of `Ω` is a product of `O(|Ω|/j)`
   elements each of which is a product of at most `j` disjoint `3`-cycles:
   decompose into disjoint cycles, write each cycle as a product of its two
   dihedral reflections, pair the transpositions of each resulting involution
   by `(ab)(cd) = (acb)(acd)`, and cut the disjoint `3`-cycles into blocks of
   `j`.  Composing the blocks with `isBoundedConjProduct_mul` turns `K(δ)`
   into `O(1/δ)`.  None of this is formalized either.

So the two missing pieces are combinatorial statements about `Equiv.Perm` of a
finite type, not analytic ones, and neither is available in the pinned
mathlib.  Recording the route here is not a substitute for proving it: row
`SO.17` stays open, and no declaration of
`Sofic/SoficEnvelopeSimplicity.lean` may be badged.
-/

namespace GroupApproximation
namespace BoundedConjProductAlgebra

open SoficEnvelopeSimplicity
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Padding and monotonicity -/

/-- One more factor may always be added, with exponent zero.  This is the
step behind monotonicity in the length. -/
theorem isBoundedConjProduct_succ_of {s : G} {K : ℕ} {a : G}
    (h : IsBoundedConjProduct s K a) : IsBoundedConjProduct s (K + 1) a :=
  (isBoundedConjProduct_succ s K a).mpr ⟨1, 0, a, Or.inl rfl, h, by simp⟩

/-- **Monotonicity in the length.**  A product of at most `K` conjugates is a
product of at most `L` conjugates for every `L ≥ K`; the unused factors are
padded with the exponent `0`. -/
theorem isBoundedConjProduct_mono {s : G} {K L : ℕ} (hKL : K ≤ L) {a : G}
    (h : IsBoundedConjProduct s K a) : IsBoundedConjProduct s L a := by
  induction L with
  | zero =>
      rwa [Nat.le_zero.mp hKL] at h
  | succ L ih =>
      rcases Nat.lt_or_ge K (L + 1) with hlt | hge
      · exact isBoundedConjProduct_succ_of (ih (Nat.lt_succ_iff.mp hlt))
      · rwa [le_antisymm hKL hge] at h

/-! ## Composition -/

/-- **Lengths add.**  This is the step that turns a decomposition of a target
into finitely many pieces, each reachable by `K` conjugates, into a single
bound: the number of factors is the sum, and in particular does not depend on
anything but the number of pieces. -/
theorem isBoundedConjProduct_mul {s : G} :
    ∀ (K L : ℕ) (a b : G), IsBoundedConjProduct s K a →
      IsBoundedConjProduct s L b → IsBoundedConjProduct s (K + L) (a * b) := by
  intro K
  induction K with
  | zero =>
      intro L a b ha hb
      rw [(isBoundedConjProduct_zero s a).mp ha, one_mul, Nat.zero_add]
      exact hb
  | succ K ih =>
      intro L a b ha hb
      obtain ⟨g, e, c, he, hc, hfac⟩ := (isBoundedConjProduct_succ s K a).mp ha
      have hlen : K + 1 + L = K + L + 1 := by omega
      rw [hlen]
      refine (isBoundedConjProduct_succ s (K + L) (a * b)).mpr
        ⟨g, e, c * b, he, ih L c b hc hb, ?_⟩
      rw [hfac, mul_assoc]

/-! ## Conjugation, on both sides -/

/-- **Conjugates of a bounded conjugate product are bounded conjugate
products of the same length.**  Conjugating each factor by the same element
leaves the number of factors and the exponents untouched.

This is what makes the *position* of a produced element irrelevant: producing
one element of a conjugacy class as a product of `K` conjugates of `s^{±1}`
produces every element of that class. -/
theorem isBoundedConjProduct_conj {s : G} :
    ∀ (K : ℕ) (a x : G), IsBoundedConjProduct s K a →
      IsBoundedConjProduct s K (x * a * x⁻¹) := by
  intro K
  induction K with
  | zero =>
      intro a x ha
      rw [(isBoundedConjProduct_zero s a).mp ha]
      exact (isBoundedConjProduct_zero s (x * 1 * x⁻¹)).mpr (by simp)
  | succ K ih =>
      intro a x ha
      obtain ⟨g, e, b, he, hb, hfac⟩ := (isBoundedConjProduct_succ s K a).mp ha
      refine (isBoundedConjProduct_succ s K (x * a * x⁻¹)).mpr
        ⟨x * g, e, x * b * x⁻¹, he, ih b x hb, ?_⟩
      rw [hfac]
      group

/-! ## Transport along homomorphisms -/

/-- A homomorphism carries a product of at most `K` conjugates of `s^{±1}` to
a product of at most `K` conjugates of `φ(s)^{±1}`, with the same length. -/
theorem isBoundedConjProduct_map {H : Type*} [Group H] (phi : G →* H)
    {s : G} :
    ∀ (K : ℕ) (a : G), IsBoundedConjProduct s K a →
      IsBoundedConjProduct (phi s) K (phi a) := by
  intro K
  induction K with
  | zero =>
      intro a ha
      refine (isBoundedConjProduct_zero (phi s) (phi a)).mpr ?_
      rw [(isBoundedConjProduct_zero s a).mp ha, map_one]
  | succ K ih =>
      intro a ha
      obtain ⟨g, e, b, he, hb, hfac⟩ := (isBoundedConjProduct_succ s K a).mp ha
      refine (isBoundedConjProduct_succ (phi s) K (phi a)).mpr
        ⟨phi g, e, phi b, he, ih b hb, ?_⟩
      rw [hfac, map_mul, map_mul, map_mul, map_inv, map_zpow]

/-! ## Commutators with `s` -/

/-- **A commutator with `s` is a product of two conjugates.**
`⁅s, g⁆ = s · (g s⁻¹ g⁻¹)` is the identity conjugate of `s` times the
`g`-conjugate of `s⁻¹`, so it has length `2` for every `g` whatsoever.

This is the production step of the elementary route to bounded normal
generation described in the module docstring: the *only* freedom is the
choice of `g`, and the length is `2` regardless of it. -/
theorem isBoundedConjProduct_commutator (s g : G) :
    IsBoundedConjProduct s 2 ⁅s, g⁆ := by
  have hinner : IsBoundedConjProduct s 1 (g * s⁻¹ * g⁻¹) :=
    (isBoundedConjProduct_succ s 0 _).mpr
      ⟨g, -1, 1, Or.inr (Or.inr rfl),
        (isBoundedConjProduct_zero s 1).mpr rfl, by rw [zpow_neg_one, mul_one]⟩
  refine (isBoundedConjProduct_succ s 1 ⁅s, g⁆).mpr
    ⟨1, 1, g * s⁻¹ * g⁻¹, Or.inr (Or.inl rfl), hinner, ?_⟩
  rw [commutatorElement_def]
  group

end BoundedConjProductAlgebra
end GroupApproximation
