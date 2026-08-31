import GroupApproximation.GGT.ElementaryHypEmbedded
import GroupApproximation.GGT.WPDElement

/-!
# Dahmani--Guirardel--Osin's Theorem 4.42, and what it buys for `E(g)`

`GGT.ElementaryHypEmbedded` split `E(g) ↪_h (G, Y)` into clause (a),
hyperbolicity of the cone-off, and clause (b), finiteness of the relative balls.
The source settles how clause (b) is actually obtained, and it is not through the
isolated-component machinery of §4.2--4.3: the proof of Theorem 6.8
(Dahmani--Guirardel--Osin, arXiv:1111.7048, p.89) opens

> Fix any point `s` of the space `S`.  We will show that the conditions (a)-(c)
> from Theorem 4.42 are satisfied.

and Theorem 4.42 lives in §4.5, the projection-complex subsection.  This module
records that theorem and proves the one step of it that needs no projection
complex at all.

## Theorem 4.42, verbatim (p.55--56)

> **Theorem 4.42.** Let `G` be a group, `{H_λ}_{λ∈Λ}` a finite collection of
> distinct subgroups of `G`.  Suppose that the following conditions hold.
>
> (a) `G` acts by isometries on a hyperbolic space `(S, d)`.
> (b) There exists `s ∈ S` such that for every `λ ∈ Λ`, the `H_λ`-orbit of `s`
>     is quasiconvex in `S`.
> (c) `{H_λ}_{λ∈Λ}` is geometrically separated.
>
> Then there exists a relative generating set `X` of `G` with respect to
> `{H_λ}_{λ∈Λ}` and a constant `α > 0` such that the Cayley graph
> `Γ(G, X ⊔ H)` is hyperbolic, and for every `λ ∈ Λ` and `h ∈ H_λ` we have
>
>     d̂_λ(1,h) ≥ α d(s, h(s)).                                          (41)
>
> In particular, if every `H_λ` acts on `S` properly, then
> `{H_λ}_{λ∈Λ} ↪_h (G, X)`.

Two quantifier shapes in that statement are load-bearing and easy to lose.
Clause (b) is `∃ s, ∀ λ` and not `∀ λ, ∃ s` --- one basepoint serves the whole
family.  And (41) is a lower bound on the *relative* distance by the orbit
displacement, so it runs from `d̂` to `d`, not the other way; the direction is
what makes the "in particular" work.

`DGOTheorem442` below states the single-subgroup case, which is the only one
needed here and in which the finiteness and distinctness of `Λ` are automatic.
Inequality (41) is expressed through `relBall`: `h ∈ D.relBall () n` says
`d̂(1,h) ≤ n`, so (41) reads `∀ n h, h ∈ D.relBall () n → α · d(s, h·s) ≤ n`.

## What is proved here

`locallyFinite_of_orbitLowerBound_of_actsProperly` --- the "in particular" of
Theorem 4.42, which is the whole of clause (b) once (41) is available and needs
none of §4.5.  The relative ball of radius `n` is contained in the set of
elements of `H` moving `s` by at most `n/α`, and properness makes that finite.
So the projection-complex machinery is needed for (41) and for hyperbolicity,
and for nothing else on this side.

## Transcription note, resolved

`GeometricallySeparatedAt` has been checked against Definition 4.40 itself
(p.54), quoted at the definition below, and one defect was found and repaired.
The rendering of `diam ≥ R` had used `∀ D ≤ R`, which is *not* implied by
`diam ≥ R` --- the supremum need not be attained.  That strengthens the
hypothesis of the implication and so weakens the predicate, which would have
made `DGOTheorem442` claim strictly more than Dahmani--Guirardel--Osin prove.
It now reads `∀ D < R`.

The remaining deviation is deliberate and is licensed by Remark 4.41 (p.55):
Definition 4.40 quantifies over every basepoint, this predicate fixes one, and
that remark shows one basepoint suffices.

## The remaining leaf for the finite-index half, and why it is that one

Condition (b) of Theorem 6.8's proof is obtained on p.89 from "`⟨h_i⟩` is of
finite index in `E(h_i)`", which is Lemma 6.5.  Its proof (p.88) runs: for
`g ∈ E⁺(h)` let `h^k(x)` be the point of the `⟨h⟩`-orbit closest to `g(x)`; then
`d(g(x), h^k(x))` is *uniformly* bounded, by `ϰ` plus the diameter of a
fundamental domain; so `g₀ = h^{-k} g` moves `x` by at most `C`, and a
thin-triangle estimate makes it move `h^N(x)` by at most `ε` as well; WPD then
puts `g₀` in a finite set, so `g` lies in finitely many cosets of `⟨h⟩`.

The step that resists here is the *uniformity* of that bound over `g ∈ E(h)`.
`CentralizerOrbitNearAxis` gives it for a fixed commuting element, but an
arbitrary `g ∈ E(h)` only satisfies `g h^n g⁻¹ = h^{±n}` for an `n` depending on
`g`, so the constant obtained that way depends on `g` too.  The honest leaf is
therefore the coarse-translation form --- every element of `E(h)` moves the
`h`-orbit along itself by a bounded amount, with one constant for the whole
subgroup --- and it is stated as `ElementaryClosureCoarseTranslation` below.
From it the WPD argument is bookkeeping: `h^{-c} g` moves every point of the
orbit by at most `K`, and `IsWPDAt` bounds how many elements can do that.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Defs

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S] [MulAction G S]

/-- **A subgroup acts properly at a basepoint**: only finitely many of its
elements move that point a bounded amount.  This is the hypothesis of the "in
particular" clause of Theorem 4.42. -/
def ActsProperlyAt (H : Subgroup G) (s : S) : Prop :=
  ∀ ε : ℝ, {g : G | g ∈ H ∧ dist s (g • s) ≤ ε}.Finite

/-- **The orbit of `s` under `H` is quasiconvex**: every geodesic between two
orbit points stays in a fixed neighbourhood of the orbit.  Condition (b) of
Theorem 4.42, in the single-subgroup case. -/
def IsQuasiconvexOrbitAt (H : Subgroup G) (s : S) : Prop :=
  ∃ σ : ℝ, 0 ≤ σ ∧ ∀ (a b : G), a ∈ H → b ∈ H →
    ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (a • s) (b • s)) →
      f 0 = a • s → f (dist (a • s) (b • s)) = b • s →
        ∀ t ∈ Set.Icc (0 : ℝ) (dist (a • s) (b • s)),
          ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ σ

/-- **Geometric separation** (Dahmani--Guirardel--Osin, Definition 4.40, p.54),
single-subgroup case at one basepoint.  Verbatim:

> Let `G` be a group acting on a space `(S,d)`.  A collection of subgroups
> `{H_λ}_{λ∈Λ}` of `G` is called *geometrically separated* if for every `ε > 0`
> and every `s ∈ S`, there exists `R > 0` such that the following holds.
> Suppose that for some `g ∈ G` and `λ, μ ∈ Λ` we have
>
>     diam (H_μ(s) ∩ (g H_λ(s))^{+ε}) ≥ R.                              (40)
>
> Then `λ = μ` and `g ∈ H_λ`.

Three points of the transcription.  The `λ = μ` clause is vacuous for a single
subgroup.  Definition 4.40 quantifies over *every* `s`, while this predicate
fixes one; Remark 4.41 (p.55) shows that verifying it at a single `s` suffices,
which is why the one-basepoint form is the one worth stating.

And `diam ≥ R` is rendered as "for every `D < R` some pair of the intersection
is at distance at least `D`", which is what `diam ≥ R` gives --- the supremum
need not be attained, so a pair at distance `≥ R` itself is *not* available.
Using `D ≤ R` there would strengthen the hypothesis of the implication, hence
weaken this predicate, hence make `DGOTheorem442` claim strictly more than the
source. The strict inequality is what keeps the citation faithful. -/
def GeometricallySeparatedAt (H : Subgroup G) (s : S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ g : G,
    (∀ D : ℝ, D < R → ∃ a b : G, a ∈ H ∧ b ∈ H ∧
      D ≤ dist (a • s) (b • s) ∧
      (∃ c : G, c ∈ H ∧ dist (a • s) ((g * c) • s) ≤ ε) ∧
      (∃ c : G, c ∈ H ∧ dist (b • s) ((g * c) • s) ≤ ε)) →
    g ∈ H

/-- **DGO Lemma 4.45, in the single-subgroup form used by Theorem 6.8.**

Assume the `H`-orbit is unbounded at the chosen basepoint.  If every point of
that orbit is also represented by the left-coset orbit `gH`, geometric
separation forces `g ∈ H`.  Equality of the two orbit sets, as in the printed
lemma, gives the displayed inclusion immediately; the one-sided formulation
is the exact amount used by the proof.

The argument is Definition 4.40 itself: take `1 • s` and an orbit point as far
away as the requested diameter, and use the two prescribed representatives in
`gH` with error zero. -/
theorem mem_of_orbit_subset_leftCosetOrbit
    (H : Subgroup G) (s : S) (g : G)
    (hsep : GeometricallySeparatedAt H s)
    (hunbounded : ∀ R : ℝ, ∃ h : G, h ∈ H ∧ R ≤ dist s (h • s))
    (hsubset : ∀ a : G, a ∈ H →
      ∃ c : G, c ∈ H ∧ a • s = (g * c) • s) :
    g ∈ H := by
  obtain ⟨R, hR, hforce⟩ := hsep 1 zero_lt_one
  apply hforce g
  intro D hDR
  obtain ⟨b, hbH, hb⟩ := hunbounded D
  obtain ⟨c₀, hc₀H, hc₀⟩ := hsubset 1 H.one_mem
  obtain ⟨c₁, hc₁H, hc₁⟩ := hsubset b hbH
  refine ⟨1, b, H.one_mem, hbH, ?_, ⟨c₀, hc₀H, ?_⟩,
    ⟨c₁, hc₁H, ?_⟩⟩
  · simpa using hb
  · rw [hc₀]
    exact dist_self _ |>.trans_le zero_le_one
  · rw [hc₁]
    exact dist_self _ |>.trans_le zero_le_one

/-- The orbit of the left coset `gH` at `s`, used as the vertex set in DGO's
projection complex.  Keeping the coset representative in the definition makes
the equivariance calculations later in §4.5 literal applications of
`mul_smul`. -/
def leftCosetOrbitAt (H : Subgroup G) (g : G) (s : S) : Set S :=
  {x | ∃ h : G, h ∈ H ∧ (g * h) • s = x}

omit [PseudoMetricSpace S] in
@[simp] theorem mem_leftCosetOrbitAt_iff
    (H : Subgroup G) (g : G) (s x : S) :
    x ∈ leftCosetOrbitAt H g s ↔
      ∃ h : G, h ∈ H ∧ (g * h) • s = x :=
  Iff.rfl

/-- **DGO Lemma 4.45, printed two-coset form.**  If the `fH`- and `gH`-orbits
at `s` agree and the subgroup orbit is unbounded, geometric separation gives
`f⁻¹g ∈ H`.  Thus equal orbit subsets cannot represent two distinct left
cosets.

The proof translates the equality by `f⁻¹` and invokes
`mem_of_orbit_subset_leftCosetOrbit`; no faithfulness of the action is assumed
or needed. -/
theorem inv_mul_mem_of_leftCosetOrbitAt_eq
    (H : Subgroup G) (s : S) (f g : G)
    (hsep : GeometricallySeparatedAt H s)
    (hunbounded : ∀ R : ℝ, ∃ h : G, h ∈ H ∧ R ≤ dist s (h • s))
    (horbit : leftCosetOrbitAt H f s = leftCosetOrbitAt H g s) :
    f⁻¹ * g ∈ H := by
  apply mem_of_orbit_subset_leftCosetOrbit H s (f⁻¹ * g) hsep hunbounded
  intro a haH
  have hfa : (f * a) • s ∈ leftCosetOrbitAt H f s :=
    ⟨a, haH, rfl⟩
  rw [horbit] at hfa
  obtain ⟨c, hcH, hfac⟩ := hfa
  refine ⟨c, hcH, ?_⟩
  have htranslated := congrArg (fun x : S => f⁻¹ • x) hfac
  simpa only [← mul_smul, inv_mul_cancel_left, mul_assoc] using htranslated.symm

end Defs

/-! ## Theorem 4.42, single subgroup -/

/-- **Dahmani--Guirardel--Osin, Theorem 4.42**, in the single-subgroup case.
See the module docstring for the verbatim statement.  Inequality (41) is
expressed through `relBall`, since `h ∈ D.relBall () n` is `d̂(1,h) ≤ n`.

This is a citation, not proved here: its proof is §4.5, the projection complex
of Bestvina--Bromberg--Fujiwara. -/
def DGOTheorem442 : Prop :=
  ∀ (G : Type u) [Group G] (S : Type v) [PseudoMetricSpace S] [MulAction G S]
    (H : Subgroup G) (s : S) (δ : ℝ),
    IsIsometricAction G S → IsHyperbolicSpace δ S →
      IsQuasiconvexOrbitAt H s → GeometricallySeparatedAt H s →
        ∃ (D : RelGenSet G Unit) (α : ℝ), 0 < α ∧
          D.fam = (fun _ => H) ∧
          (∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet)) ∧
          ∀ (n : ℕ) (h : G), h ∈ D.relBall () n → α * dist s (h • s) ≤ (n : ℝ)

/-! ## The "in particular" clause, proved -/

section InParticular

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S] [MulAction G S]

/-- **Clause (b) from inequality (41) and properness.**  This is the "in
particular" of Theorem 4.42 and it needs no projection complex: the relative
ball of radius `n` is contained in the set of elements of `H` moving `s` by at
most `n/α`, which properness makes finite.

So the whole cost of local finiteness is (41); everything after it is this
containment. -/
theorem locallyFinite_of_orbitLowerBound_of_actsProperly
    {D : RelGenSet G Unit} {H : Subgroup G} (hfam : D.fam = fun _ => H)
    {s : S} {α : ℝ} (hα : 0 < α)
    (hlow : ∀ (n : ℕ) (h : G), h ∈ D.relBall () n → α * dist s (h • s) ≤ (n : ℝ))
    (hproper : ActsProperlyAt H s) :
    ∀ n : ℕ, (D.relBall () n).Finite := by
  intro n
  refine Set.Finite.subset (hproper ((n : ℝ) / α)) ?_
  intro h hh
  have hfam' : D.fam () = H := congrFun hfam ()
  refine ⟨?_, ?_⟩
  · have hmem := (RelGenSet.mem_relBall.mp hh).1
    rw [hfam'] at hmem
    exact hmem
  · rw [le_div_iff₀ hα]
    calc dist s (h • s) * α = α * dist s (h • s) := mul_comm _ _
      _ ≤ (n : ℝ) := hlow n h hh

/-- **`H ↪_h (G, D.base)` from Theorem 4.42's output and properness.**  The two
clauses of `IsHyperbolicallyEmbedded` are the hyperbolicity `DGOTheorem442`
returns and the local finiteness just proved. -/
theorem isHypEmbeddedOf_of_orbitLowerBound_of_actsProperly
    {D : RelGenSet G Unit} {H : Subgroup G} (hfam : D.fam = fun _ => H)
    {s : S} {α : ℝ} (hα : 0 < α)
    (hhyp : ∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet))
    (hlow : ∀ (n : ℕ) (h : G), h ∈ D.relBall () n → α * dist s (h • s) ≤ (n : ℝ))
    (hproper : ActsProperlyAt H s) :
    IsHypEmbeddedOf G D.base H :=
  ⟨D, rfl, hfam, ⟨hhyp,
    fun _ n =>
      locallyFinite_of_orbitLowerBound_of_actsProperly hfam hα hlow hproper n⟩⟩

/-- **The whole of Theorem 4.42's consequence, assembled.**  Given the citation,
quasiconvexity, geometric separation and properness deliver
`H ↪_h G`. -/
theorem isHypEmbedded_of_dgo442 (h442 : DGOTheorem442.{u, v})
    (H : Subgroup G) (s : S) (δ : ℝ) (hiso : IsIsometricAction G S)
    (hδ : IsHyperbolicSpace δ S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) (hproper : ActsProperlyAt H s) :
    IsHypEmbedded G H := by
  obtain ⟨D, α, hα, hfam, hhyp, hlow⟩ := h442 G S H s δ hiso hδ hqc hsep
  exact (isHypEmbeddedOf_of_orbitLowerBound_of_actsProperly hfam hα hhyp hlow
    hproper).isHypEmbedded

end InParticular

/-! ## The remaining leaf for the finite-index half -/

section Leaf

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Every element of `E(h)` moves the `h`-orbit along itself by a bounded
amount, with one constant for the whole subgroup.**

This is the uniformity in Dahmani--Guirardel--Osin's Lemma 6.5 (p.88), where the
bound is "`ϰ` plus the diameter of a fundamental domain for the action of `h` on
its quasi-axis" and is visibly independent of the element of `E(h)` chosen.
`CentralizerOrbitNearAxis` does not supply it: an arbitrary `g ∈ E(h)` satisfies
`g h^n g⁻¹ = h^{±n}` only for an `n` depending on `g`, so the constant obtained
from the commuting case depends on `g`.

From this the finite-index half is bookkeeping against `IsWPDAt`: `h^{-c} g`
moves every point of the orbit by at most `K`, and `IsWPDAt` bounds how many
elements can move two far-apart orbit points that little, so `E(h)` meets
finitely many cosets of `⟨h⟩`. -/
def ElementaryClosureCoarseTranslation (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ h : G, IsLoxodromic h x → ∃ K : ℝ, 0 ≤ K ∧
    ∀ g : G, g ∈ elementaryClosure h →
      ∃ (e : ℤ) (c : ℤ), (e = 1 ∨ e = -1) ∧
        ∀ m : ℤ, dist ((g * h ^ m) • x) ((h ^ (e * m + c)) • x) ≤ K


/-! ### The WPD bookkeeping, proved

What the leaf is for.  Once an element of `E(h)` is known to move the `h`-orbit
along itself by at most `K`, subtracting the shift produces an element that
almost fixes *every* point of the orbit, in particular the two points `x` and
`h^M x` that `IsWPDAt` separates.  So the whole subgroup meets only finitely
many cosets of `⟨h⟩`, which is the finite-index half.

This is the derivation from the leaf, and it is unconditional in everything
else. -/

/-- **From bounded shift to a finite transversal.**  An element `g` that carries
the `h`-orbit to itself with shift `c` and error `K` differs from `h^c` by an
element of the `K`-pair-stabiliser of `x` and `h^M x`, which `IsWPDAt` makes
finite.  So all such `g` lie in finitely many cosets of `⟨h⟩`.

No loxodromy, no acylindricity and no hyperbolicity are used: the entire content
is `IsWPDAt` plus the isometry of the action. -/
theorem exists_finite_transversal_of_coarseTranslation
    (hiso : IsIsometricAction G X) {h : G} {x : X} (hwpd : IsWPDAt h x)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ F : Set G, F.Finite ∧
      ∀ g : G, (∃ c : ℤ, ∀ m : ℤ,
          dist ((g * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K) →
        ∃ (c : ℤ) (f : G), f ∈ F ∧ g = h ^ c * f := by
  obtain ⟨M, hMfin⟩ := hwpd K hK
  refine ⟨pairStab G K x ((h ^ M) • x), hMfin, ?_⟩
  rintro g ⟨c, hc⟩
  refine ⟨c, h ^ (-c) * g, ?_, by group⟩
  rw [mem_pairStab]
  constructor
  · have h0 := hc 0
    rw [zpow_zero, mul_one, zero_add] at h0
    have hl : (h ^ (-c)) • (g • x) = (h ^ (-c) * g) • x := (mul_smul _ _ _).symm
    have hr : (h ^ (-c)) • ((h ^ c) • x) = x := by
      rw [← mul_smul, ← zpow_add]
      simp
    have hshift := hiso (h ^ (-c)) (g • x) ((h ^ c) • x)
    rw [hl, hr] at hshift
    rw [dist_comm, hshift]
    exact h0
  · have hM := hc (M : ℤ)
    have hl : (h ^ (-c)) • ((g * h ^ (M : ℤ)) • x)
        = (h ^ (-c) * g) • ((h ^ M) • x) := by
      rw [← mul_smul, ← mul_smul, zpow_natCast, mul_assoc]
    have hr : (h ^ (-c)) • ((h ^ ((M : ℤ) + c)) • x) = (h ^ M) • x := by
      rw [← mul_smul, ← zpow_add]
      have he : -c + ((M : ℤ) + c) = (M : ℤ) := by ring
      rw [he, zpow_natCast]
    have hshift := hiso (h ^ (-c)) ((g * h ^ (M : ℤ)) • x)
      ((h ^ ((M : ℤ) + c)) • x)
    rw [hl, hr] at hshift
    rw [dist_comm, hshift]
    exact hM

/-- **The leaf and the transversal, packaged at one constant.**

The leaf supplies, for each `g ∈ E(h)`, a sign and a shift with error `K`; the
transversal theorem consumes exactly the sign-`+1` case at that same `K`.  Both
are returned together so a consumer can take an element of `E(h)`, read off its
sign, and in the orientation-preserving case land it in finitely many cosets of
`⟨h⟩`.

The orientation-reversing case is an index-at-most-two argument — a product of
two reversing elements preserves orientation, so they form at most one further
coset — and is not carried out here.  It is bookkeeping about the sign rather
than geometry, and with the leaf available it is the only part of
Dahmani--Guirardel--Osin's Lemma 6.5 still open. -/
theorem exists_finite_transversal_of_positivePart
    (hiso : IsIsometricAction G X) {h : G} {x : X} (hwpd : IsWPDAt h x)
    (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x) :
    ∃ (K : ℝ) (F : Set G), 0 ≤ K ∧ F.Finite ∧
      (∀ g : G, g ∈ elementaryClosure h →
        ∃ e c : ℤ, (e = 1 ∨ e = -1) ∧
          ∀ m : ℤ, dist ((g * h ^ m) • x) ((h ^ (e * m + c)) • x) ≤ K) ∧
      (∀ g : G, (∃ c : ℤ, ∀ m : ℤ,
          dist ((g * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K) →
        ∃ (c : ℤ) (f : G), f ∈ F ∧ g = h ^ c * f) := by
  obtain ⟨K, hK0, hK⟩ := hct h hlox
  obtain ⟨F, hFfin, hF⟩ :=
    exists_finite_transversal_of_coarseTranslation hiso hwpd hK0
  exact ⟨K, F, hK0, hFfin, hK, hF⟩

end Leaf

end Elementary
end GGT
end GroupApproximation
