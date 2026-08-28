import GroupApproximation.GGT.RelHypDefinition

/-!
# Ping-pong: a free subgroup of rank two, and the two forms consumers ask for

Gromov, *Hyperbolic groups*, §8.2; Delzant, *Sous-groupes distingués et
quotients des groupes hyperboliques*.  A group acting on a hyperbolic space
with two independent loxodromic elements contains a free subgroup of rank two,
by ping-pong on high powers of the two elements.  For a hyperbolic group acting
on its own Cayley graph this is the Tits alternative in the form usually
quoted: a non-elementary hyperbolic group contains `F₂`.

This module states that input once, in the two forms its consumers ask for, so
that no lane restates it.

## Who consumes it

* **`GGT.RelHyp`** (`GGT/RelHypOsinTheorem24.lean`), through
  `PingPongFreeSubgroup`: `OsinRelatorDesign` needs two elements of `H₀`
  generating a free subgroup, to build Fournier-Facio's relators `u_k · w_k⁻¹`
  with `w_k = a b^{n_1} a b^{n_2} ⋯` and to know that the four letters
  `a, a⁻¹, b, b⁻¹` are pairwise distinct.
* **`GGT` (ggt-wpd)**, through `noCommonZpow_of_injective` and its packaged
  form `exists_noCommonZpow_of_freeRankTwo`, whose conclusion
  `∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0` is verbatim the `hab` hypothesis
  of `WPDAcylindricalHyperbolicity.actsNonElementarily_of_no_common_power` and
  of `not_isVirtuallyCyclic_of_no_common_power`.  That corollary is proved
  below, so ggt-wpd's hypothesis is discharged by whoever supplies the input,
  and neither lane has to name a free-subgroup statement of its own.

`GGT.Elementary` (ggt-elementary) is **not** a consumer, and this module does
not claim it as one.  Their two residuals, `CentralizerOrbitNearAxis` and
`EscapingBoundedTurn`, are orbit-stability estimates near an axis; neither
mentions free subgroups and neither would follow from this.  Different content,
different proof.

## Which form, and one correction worth recording

Two statements travel under "ping-pong gives a free subgroup", and they are not
the same input.

* `PingPongFreeSubgroup` -- **existence only**: an injective
  `φ : FreeGroup (Fin 2) →* H`.  Nothing metric.
* `UndistortedPingPongFreeSubgroup` -- the **quantitative** form: the same `φ`
  together with two-sided linear comparison between the `F₂`-word length and
  the `X`-word length of the image, i.e. the free subgroup is undistorted.

**BOTH are needed, and an earlier version of this docstring said otherwise.**
The correction is recorded here rather than silently edited away, because the
mistake is the natural one and the reasoning that produced it is still half
right.

What is right: the *piece* condition needs only the qualitative form.
`OsinWeightedMetric.LetterMetricSmallCancellation` compares list lengths on both
sides of `p.length < lam * r.length`, and those lists are chosen by the design,
not read off geodesics, so the bound on a piece is word combinatorics and the
only thing needed of the ambient group is that distinct letter symbols name
distinct elements -- injectivity of `φ`.

What is wrong: the piece condition is not the only clause.
`GGT/RelHypOsinTheorem24Refuted.lean` shows `WeightedGreendlingerLeaf` is FALSE
without a further clause, namely that each relator be a **geodesic word**,
`LetterGeodesic L r : r.length = L.len r.prod`.  And geodesicity is exactly a
*lower* bound on the alphabet-length of the element a relator spells, which is
undistortedness of the subgroup the relator is built in.  A design whose
relators are words in `⟨a, b⟩` is geodesic only if `⟨a, b⟩` is undistorted in
the ambient generating set; otherwise a shorter spelling exists outside the
subgroup and the relator's 42 letters overstate its relative length.  That is
precisely the witness of the refutation, at `⟨t⟩ ≤ ℤ` with `t^42` in the
alphabet.

So: `PingPongFreeSubgroup` is what the metric certificate needs, and
`UndistortedPingPongFreeSubgroup` is what the geodesicity certificate needs.
Prove both.  They are still different theorems with different proofs -- ping-pong
on high powers, versus ping-pong plus the Morse lemma -- and a lane that needs
only the first should still take only the first.

## The proof plan

Ping-pong on high powers of two independent loxodromics `g, h`: independence
bounds the Gromov products of their orbits, so for large `M` the sets
"points nearer the `g`-axis than the `h`-axis" and its mirror are swapped in
the pattern the ping-pong lemma needs, and `⟨g^M, h^M⟩` is free of rank two.
The quantitative input is orbit control near an axis, which is the same
ingredient the Morse plan of `GGT.Elementary` is built on --
`Elementary.CentralizerOrbitNearAxis` is the statement of that shape already in
the tree -- but the ping-pong argument uses it for a *different* conclusion, so
neither lane's residual implies the other's.

None of the three inputs is proved here.  What *is* proved is what follows
from an input once it is supplied: the corollaries of section 2, which are the
shapes the two consumers apply, and the design arithmetic of section 3.
-/

namespace GroupApproximation
namespace GGT
namespace PingPong

universe u

/-! ## 1.  The conclusion, and the two forms of the input -/

/-- **A free subgroup of rank two**, as an injective homomorphism from the free
group on two generators.  Stated as a homomorphism rather than as a `Subgroup`
so that its two generators are named and can be used as letters. -/
def FreeRankTwo (G : Type u) [Group G] : Prop :=
  ∃ φ : FreeGroup (Fin 2) →* G, Function.Injective φ

/-- The first generator of a rank-two free subgroup. -/
def gen₀ {G : Type u} [Group G] (φ : FreeGroup (Fin 2) →* G) : G :=
  φ (FreeGroup.of 0)

/-- The second generator of a rank-two free subgroup. -/
def gen₁ {G : Type u} [Group G] (φ : FreeGroup (Fin 2) →* G) : G :=
  φ (FreeGroup.of 1)

/-- **The input, group form.**  A non-elementary torsion-free hyperbolic group
contains a free subgroup of rank two.  This is what
`GGT/RelHypOsinTheorem24.lean`'s `OsinRelatorDesign` needs, and it is the
qualitative form: no metric comparison. -/
def PingPongFreeSubgroup : Prop :=
  ∀ (H : Type) (_ : Group H),
    Infinite H → IsPowerTorsionFree H → Hyperbolic.IsHyperbolicGroup H →
      ¬ RelHyp.IsElementaryGroup H → FreeRankTwo H

/-- **The input, action form.**  A group acting by isometries on a hyperbolic
space with two independent loxodromics contains a free subgroup of rank two.
The group form is its special case at the action of a hyperbolic group on its
own Cayley graph.

**This form currently has no consumer**, and the reason is worth recording.  It
was offered to ggt-wpd, whose lane sits strictly *upstream* of non-elementarity:
their consumer is Osin's Lemma 5.12, whose conclusion is
`ActsNonElementarily ⊤ (Cayley.base _)`, so feeding them a statement that takes
`ActsNonElementarily` as a hypothesis would assume what they are proving.  Any
lane below non-elementarity should take this form; any lane above it, or at it,
must not. -/
def PingPongFreeSubgroupGeometric : Prop :=
  ∀ (G : Type) (_ : Group G) (X : Type) (_ : PseudoMetricSpace X)
    (_ : MulAction G X) (delta : ℝ) (x : X),
      HullGeometry.IsIsometricAction G X →
        HullGeometry.IsHyperbolicSpace delta X →
          HullGeometry.ActsNonElementarily (⊤ : Subgroup G) x →
            FreeRankTwo G

/-- **The quantitative form**, for lanes that genuinely need to compare the two
metrics: the free subgroup is undistorted, with explicit two-sided constants
against the word metric of a finite alphabet `S`.

This is what the **geodesicity** clause of the repaired Greendlinger leaf needs:
`LetterGeodesic L r` is a lower bound on the alphabet-length of the element `r`
spells, and a relator built inside `⟨a, b⟩` meets it only if `⟨a, b⟩` is
undistorted.  It is strictly harder than the qualitative form -- ping-pong plus
the Morse lemma, against ping-pong alone -- so a lane that needs only the metric
certificate should still take `PingPongFreeSubgroup`. -/
def UndistortedPingPongFreeSubgroup : Prop :=
  ∀ (H : Type) (_ : Group H) (S : Finset H),
    WordMetric.IsSymmetricGeneratingSet (S : Set H) →
      Infinite H → IsPowerTorsionFree H → Hyperbolic.IsHyperbolicGroup H →
        ¬ RelHyp.IsElementaryGroup H →
          ∃ (φ : FreeGroup (Fin 2) →* H) (_ : Function.Injective φ)
            (lam c : ℚ), 0 < lam ∧
              ∀ w : FreeGroup (Fin 2),
                (lam : ℚ) * (FreeGroup.norm w : ℚ) - c
                    ≤ (WordMetric.wordNorm (S : Set H) (φ w) : ℚ) ∧
                  (WordMetric.wordNorm (S : Set H) (φ w) : ℚ)
                    ≤ (FreeGroup.norm w : ℚ) / lam + c

/-! ## 2.  What the input buys, proved -/

/-- **The two generators have no common nonzero power.**

This is the exact shape of the `hab` hypothesis of
`GGT.actsNonElementarily_of_no_common_power` and of
`GGT.not_isVirtuallyCyclic_of_no_common_power`, so a consumer of the input
never has to unfold `FreeRankTwo`.

The proof is one homomorphism: kill the second generator, send the first to a
generator of `ℤ`, and read off the exponent. -/
theorem noCommonZpow_of_injective {G : Type u} [Group G]
    (φ : FreeGroup (Fin 2) →* G) (hφ : Function.Injective φ) (m k : ℤ)
    (h : gen₀ φ ^ m = gen₁ φ ^ k) : m = 0 ∧ k = 0 := by
  have hfree : (FreeGroup.of (0 : Fin 2)) ^ m = (FreeGroup.of (1 : Fin 2)) ^ k := by
    apply hφ
    rw [map_zpow, map_zpow]
    exact h
  constructor
  · have hmap := congrArg (FreeGroup.lift fun i : Fin 2 =>
      if i = 0 then Multiplicative.ofAdd (1 : ℤ) else 1) hfree
    rw [map_zpow, map_zpow] at hmap
    have htoAdd := congrArg Multiplicative.toAdd hmap
    simpa using htoAdd
  · have hmap := congrArg (FreeGroup.lift fun i : Fin 2 =>
      if i = 1 then Multiplicative.ofAdd (1 : ℤ) else 1) hfree
    rw [map_zpow, map_zpow] at hmap
    have htoAdd := congrArg Multiplicative.toAdd hmap
    simpa using htoAdd

/-- The same, packaged at an existential witness. -/
theorem exists_noCommonZpow_of_freeRankTwo {G : Type u} [Group G]
    (h : FreeRankTwo G) :
    ∃ a b : G, ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0 := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨gen₀ φ, gen₁ φ, noCommonZpow_of_injective φ hφ⟩

/-! ## 3.  The design arithmetic

The relator family of `OsinRelatorDesign` is, for each generator `u_k` of the
peripheral factor, the letter list

    u_k · b^{-n_m} a⁻¹ ⋯ b^{-n_1} a⁻¹

of `1 + m + Σ nᵢ` letters, symmetrized by rotation and formal inversion.  With
all block sizes across the whole family pairwise distinct and lying in
`[N, 2N]`, a common prefix of two distinct members contains at most one `a`:
two `a`'s would force a full block of one relator to match a full block of the
other, hence the blocks to be equal, hence the members to be equal.  So a piece
has at most `2·(2N) + 1` letters, and `C'(1/8)` is the inequality below.

The two lemmas here are the arithmetic of that count.  The combinatorics itself
-- "a common prefix with two `a`'s forces equal blocks" -- is the remaining
work, and it needs no geometry at all. -/

/-- The letter length of a block relator with `m` blocks of size at most `2N`
and at least `N`. -/
def blockRelatorLength (m N : ℕ) : ℕ := 1 + m + m * N

/-- **The length floor.**  Thirty-three blocks of size at least one already
clear the design's floor of `42` letters. -/
theorem le_blockRelatorLength {m N : ℕ} (hN : 1 ≤ N) (hm : 33 ≤ m) :
    42 ≤ blockRelatorLength m N := by
  have h : 33 * 1 ≤ m * N := Nat.mul_le_mul hm hN
  unfold blockRelatorLength
  omega

/-- **The piece bound clears `C'(1/8)`.**  A piece spans at most one separator
and two partial blocks, so at most `2·(2N) + 1` letters, and thirty-three
blocks make that less than an eighth of the relator. -/
theorem pieceBound_lt_eighth {m N : ℕ} (hN : 1 ≤ N) (hm : 33 ≤ m) :
    8 * (2 * (2 * N) + 1) < blockRelatorLength m N := by
  have h : 33 * N ≤ m * N := Nat.mul_le_mul hm (le_refl N)
  unfold blockRelatorLength
  omega

end PingPong
end GGT
end GroupApproximation
