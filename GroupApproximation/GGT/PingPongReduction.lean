import GroupApproximation.GGT.PingPongFreeSubgroup

/-!
# Ping-pong: the table, the lemma, and the reduction to `FreeRankTwo`

`GGT/PingPongFreeSubgroup.lean` states the free-subgroup input and proves what
follows from it.  This module takes it apart: the input is reduced here to three
named `Prop`s, two of which are not group theory at all, so that the geometric
content is isolated and can be attacked on its own.

## The three inputs, and how much of each is really open

* `PingPongLemmaStatement` — **the ping-pong lemma itself**: two elements with a
  ping-pong table generate freely.  This is a lemma about a group action on a
  set with no geometry in it, and **Mathlib has it**; the search term is
  `FreeGroup.injective_lift_of_ping_pong` (and its free-product sibling
  `Monoid.CoprodI.lift_injective_of_ping_pong`), whose exact signature this
  author could not verify without a compiler.  It is stated as a `Prop` so that
  the reduction below can be landed now, and it should be discharged **by
  lookup, not by proof** — anyone with a build should replace it in one line.
* `PingPongTableStatement` — **the geometry**: two independent loxodromics have
  high powers that admit a ping-pong table.  This is the only genuinely open
  input, and it is the one the Morse machinery of `GGT.Elementary` is for.
* `CayleyHyperbolicSpaceStatement` and `NonElementaryActsStatement` — the two
  bridges the *group* form needs on top of the action form.  The first is
  elementary and is not a citation (see below); the second is Osin's
  Theorem 1.1.

## The proof plan for the open one

Take `C` from `Independent g h x` and `δ` from hyperbolicity, and set

    A = { y | ∃ n ≠ 0, C + δ < (y | gⁿ·x)_x },
    B = { y | ∃ m ≠ 0, C + δ < (y | hᵐ·x)_x }.

*Disjoint*: a point in both gives `min ((y|gⁿx)_x) ((y|hᵐx)_x) > C + δ`, and the
four-point condition then puts `(gⁿx | hᵐx)_x > C`, contradicting independence.
This is where the `+ δ` in the definition is spent, and it is the reason the
sets cannot be defined with the bare constant.

*Nonempty*: `g^N · x ∈ A` for large `N`, since `(g^N x | g^N x)_x = d(x, g^N x)`
grows linearly by loxodromy.

*Ping-pong*: for `z ∈ B` and `n ≠ 0`, the point `g^{Mn} · z` is far along the
`g`-direction because `z` is not, which is the orbit-stability estimate
`Elementary.CentralizerOrbitNearAxis` is shaped for.  `M` is chosen so that the
translation length of `g^M` exceeds the constants.

Nothing above is proved here.  What is proved is that these inputs suffice.

## What is proved

* `freeRankTwo_of_pingPong` — a single ping-pong table gives `FreeRankTwo`.
* `gen₀_lift_pairMap`, `gen₁_lift_pairMap` — the free pair produced *is* the
  ping-pong pair, so a consumer of `gen₀`/`gen₁` gets the elements it played
  with, not merely some pair.
* `pingPongFreeSubgroupGeometric_of` — the action form, from two inputs.
* `pingPongFreeSubgroup_of` — the group form, from four.

`PingPong.FreeRankTwo`, `gen₀`, `gen₁`, `noCommonZpow_of_injective` and
`exists_noCommonZpow_of_freeRankTwo` are load-bearing for ggt-wpd on main and
are not touched here.
-/

namespace GroupApproximation
namespace GGT
namespace PingPong

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## 1.  The table -/

/-- **A ping-pong table for two elements**: two disjoint nonempty sets, each
swallowed by every nonzero power of the *other* element's partner.  The
asymmetry of the two clauses is the usual one and is what the lemma needs. -/
def IsPingPongPair {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (a b : G) (A B : Set X) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    (∀ n : ℤ, n ≠ 0 → ∀ z ∈ B, (a ^ n) • z ∈ A) ∧
    (∀ n : ℤ, n ≠ 0 → ∀ z ∈ A, (b ^ n) • z ∈ B)

/-- The two players as a family indexed by `Fin 2`, so that `FreeGroup.lift`
applies to them. -/
def pairMap {G : Type u} [Group G] (a b : G) : Fin 2 → G :=
  fun i => if i = 0 then a else b

theorem pairMap_zero {G : Type u} [Group G] (a b : G) : pairMap a b 0 = a := by
  simp [pairMap]

theorem pairMap_one {G : Type u} [Group G] (a b : G) : pairMap a b 1 = b := by
  simp [pairMap]

/-! ## 2.  The ping-pong lemma, as a named input -/

/-- **The ping-pong lemma.**  Two elements admitting a ping-pong table generate
a free group of rank two.

No geometry, no hyperbolicity: an action on a bare set.  Mathlib has this — see
the module docstring — and this `Prop` exists only so that the reduction can be
landed before the lookup is done. -/
def PingPongLemmaStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (X : Type v) (_ : MulAction G X) (a b : G)
    (A B : Set X), IsPingPongPair a b A B →
      Function.Injective (FreeGroup.lift (pairMap a b))

/-! ## 3.  The reduction -/

/-- **A ping-pong table gives a free subgroup of rank two.** -/
theorem freeRankTwo_of_pingPong (hPP : PingPongLemmaStatement.{u, v})
    {G : Type u} [Group G] {X : Type v} [MulAction G X] {a b : G} {A B : Set X}
    (h : IsPingPongPair a b A B) : FreeRankTwo G :=
  ⟨FreeGroup.lift (pairMap a b), hPP G inferInstance X inferInstance a b A B h⟩

/-- The first generator of the free subgroup is the first player. -/
theorem gen₀_lift_pairMap {G : Type u} [Group G] (a b : G) :
    gen₀ (FreeGroup.lift (pairMap a b)) = a := by
  simp [gen₀, pairMap]

/-- The second generator of the free subgroup is the second player. -/
theorem gen₁_lift_pairMap {G : Type u} [Group G] (a b : G) :
    gen₁ (FreeGroup.lift (pairMap a b)) = b := by
  simp [gen₁, pairMap]

/-! ## 4.  The geometric input -/

/-- **The open input.**  Two independent loxodromics have high powers admitting
a ping-pong table.

This is the whole of the geometry, and the proof plan is in the module
docstring: the two sets are the "toward the `g`-end" and "toward the `h`-end"
cones cut out by the Gromov product at the basepoint, disjoint because
independence bounds the product of the two orbits, and swallowing because a high
power of a loxodromic drags any point that is not already in its cone into
it. -/
def PingPongTableStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (X : Type v) (_ : PseudoMetricSpace X)
    (_ : MulAction G X) (delta : ℝ) (x : X),
      IsIsometricAction G X → IsHyperbolicSpace delta X →
        ∀ g h : G, IsLoxodromic g x → IsLoxodromic h x → Independent g h x →
          ∃ (M : ℕ) (A B : Set X), 0 < M ∧ IsPingPongPair (g ^ M) (h ^ M) A B

/-- **The action form, reduced.**  Non-elementarity hands over two independent
loxodromics; the geometry turns them into a table; the ping-pong lemma turns the
table into a free pair. -/
theorem pingPongFreeSubgroupGeometric_of (hPP : PingPongLemmaStatement.{u, v})
    (hTable : PingPongTableStatement.{u, v}) :
    PingPongFreeSubgroupGeometric.{u, v} := by
  intro G instG X instX instA delta x hiso hhyp hne
  obtain ⟨g, -, h, -, hg, hh, hind⟩ := hne
  obtain ⟨M, A, B, -, htable⟩ :=
    hTable G instG X instX instA delta x hiso hhyp g h hg hh hind
  exact freeRankTwo_of_pingPong hPP htable

/-! ## 5.  The two bridges the group form needs -/

/-- **The Cayley graph of a word-hyperbolic group is a hyperbolic space.**

This is *not* a citation.  `Algebra/HyperbolicGroup.lean` defines
`IsHyperbolicGroup` by the four-point condition on the `ℕ`-valued word metric,
and `isFourPointHyperbolic_iff_gromovProduct` already rearranges that into the
Gromov-product form; `HullGeometry.IsHyperbolicSpace` is the same inequality on
the `ℝ`-valued metric of `Cayley`, with the two products halved and the roles of
the last two points exchanged.  So the content is a change of variables and a
cast, and it is stated as a `Prop` only because it has not been written. -/
def CayleyHyperbolicSpaceStatement : Prop :=
  ∀ (G : Type u) (_ : Group G), Hyperbolic.IsHyperbolicGroup G →
    ∃ (A : Alphabet G) (delta : ℝ), IsHyperbolicSpace delta (Cayley A)

/-- **Osin's Theorem 1.1, the direction the group form needs**: an infinite
hyperbolic group that is not virtually cyclic acts non-elementarily on its own
Cayley graph.

`GGT.actsNonElementarily_of_no_common_power` is the *other* end of the same
trichotomy — it produces non-elementarity from a common-power-free pair — so
this statement and that theorem must not be confused for each other, and a lane
sitting upstream of non-elementarity must consume neither. -/
def NonElementaryActsStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (A : Alphabet G) (delta : ℝ),
    IsHyperbolicSpace delta (Cayley A) → Infinite G →
      ¬ RelHyp.IsElementaryGroup G →
        ActsNonElementarily (⊤ : Subgroup G) (Cayley.base A)

/-- **The group form, reduced.**  Four named inputs, of which one is a lookup in
Mathlib, one is elementary, one is Osin's Theorem 1.1, and one — the table — is
the geometry. -/
theorem pingPongFreeSubgroup_of (hPP : PingPongLemmaStatement.{u, u})
    (hTable : PingPongTableStatement.{u, u})
    (hCay : CayleyHyperbolicSpaceStatement.{u})
    (hNE : NonElementaryActsStatement.{u}) : PingPongFreeSubgroup.{u} := by
  intro H instH hinf _htf hhyp hnel
  obtain ⟨A, delta, hhypsp⟩ := hCay H instH hhyp
  exact pingPongFreeSubgroupGeometric_of hPP hTable H instH (Cayley A)
    inferInstance inferInstance delta (Cayley.base A)
    (isIsometricAction_cayley A) hhypsp (hNE H instH A delta hhypsp hinf hnel)

end PingPong
end GGT
end GroupApproximation
