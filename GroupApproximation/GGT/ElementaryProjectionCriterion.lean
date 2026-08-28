import GroupApproximation.GGT.ElementaryHypEmbedded

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

## Transcription note

`GeometricallySeparatedAt` is transcribed from the *use* of Definition 4.40 in
Remark 4.41 (p.55), not from Definition 4.40 itself, which is on an earlier page
I have not read.  Remark 4.41 uses it in the form: for every `ε > 0` and some
`s`, there is `R = R(ε) > 0` such that
`diam (H_μ(s) ∩ (g H_λ(s))^{+ε}) ≥ R` forces `λ = μ` and `g ∈ H_λ`.  In the
single-subgroup case the `λ = μ` clause is vacuous and only `g ∈ H` survives.
This should be checked against Definition 4.40 before anything is proved *from*
it; nothing here is.

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

/-- **Geometric separation**, single-subgroup case, transcribed from the use of
Definition 4.40 in Remark 4.41 (p.55): distinct translates of the orbit have
uniformly bounded coarse intersection.  See the transcription note in the module
docstring --- this is read off a remark rather than off the definition. -/
def GeometricallySeparatedAt (H : Subgroup G) (s : S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ g : G,
    (∀ D : ℝ, D ≤ R → ∃ a b : G, a ∈ H ∧ b ∈ H ∧
      D ≤ dist (a • s) (b • s) ∧
      (∃ c : G, c ∈ H ∧ dist (a • s) ((g * c) • s) ≤ ε) ∧
      (∃ c : G, c ∈ H ∧ dist (b • s) ((g * c) • s) ≤ ε)) →
    g ∈ H

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

end Leaf

end Elementary
end GGT
end GroupApproximation
