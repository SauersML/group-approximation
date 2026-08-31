import GroupApproximation.GGT.HullSCConeOffCyclicReduction
import GroupApproximation.GGT.HullSCConeOffHeavyNonComm
import GroupApproximation.GGT.HullYiFiniteRadicalDetector
import GroupApproximation.GGT.HullYiCyclicOrientation
import GroupApproximation.GGT.HullYiMatchedProductRigidity
import GroupApproximation.GGT.DGOCorollary66

/-!
# Hull's `nonelsub` and `yi`, as statements, and what they close

Hull, *Small cancellation in acylindrically hyperbolic groups* (arXiv:1308.4345),
§5.  Two lemmas stand between a suitable subgroup and the cyclic hyperbolically
embedded subgroups Theorem 5.1 runs over:

> **`nonelsub`.**  If `S` is non-elementary then for all `k ≥ 1`, `S` contains
> pairwise non-commensurable loxodromic `f₁,…,f_k` with `E_G(fᵢ) = E_G⁺(fᵢ)`.
>
> **`yi`.**  If `S` is non-elementary then there are non-commensurable
> loxodromic `h₁,…,h_m` with `E_G(hᵢ) = ⟨hᵢ⟩ × K_G(S)`.
>
> **`suitsubc`.**  If `S` is suitable then for all `k`, `S` contains
> non-commensurable loxodromic `h₁,…,h_k` with `E_G(hᵢ) = ⟨hᵢ⟩`; in particular
> `{⟨h₁⟩,…,⟨h_k⟩} ↪_h (G, 𝒜)`.

`suitsubc` at `k = 2` is `ExistsHypEmbeddedConeOff₂`, the one geometric clause
left of the Hull row of `Manuscript/NonMF/TheoremCDebts.lean`.  This module
states `nonelsub` and `yi` in the repository's vocabulary and **proves the
passage from `yi` to that clause**, so the row closes by instantiation the day
`yi` is proved.

## Scope, and why each clause is the one carried

* **`yi` is stated in the suitable case only**, where `K_G(S) = 1` and its
  conclusion reads `E_G(h) = ⟨h⟩`.  The general `⟨h⟩ × K_G(S)` needs a direct
  product decomposition whose only consumer would be the case `K_G(S) = 1`;
  `GGT/HullYiLoxRadical.lean` already proves the triviality this rests on
  (`loxRadical_eq_bot_of_suitable`), and it does so quantified over *every*
  loxodromic of `S`.  `exists_finite_loxodromic_family_trivial_intersection`
  now also proves the finite-family detection step in Hull's proof, so this
  passage needs neither `nonelsub` nor DGO 6.12.
* **Non-commensurability carries its conjugator.**  `∀ c p q, c⁻¹fᵖc ≠ gᑫ` and
  not the weak `∀ p q, fᵖ ≠ gᑫ`: the weak form admits conjugate loxodromics,
  and `GGT/HullYiNonCommensurable.lean` proves a family containing a conjugate
  pair is *never* hyperbolically embedded, so `heGX` cannot hold for the weak
  form.  This is a theorem about the statement, not a stylistic choice.
* **`nonelsub`'s fourth clause, `E_G(fᵢ) = E_G⁺(fᵢ)`, is carried.**  The
  repository now has the exact vocabulary in
  `GGT.Elementary.positiveElementaryClosure` and the centralizer theorem in
  `DGOCorollary66`; dropping the clause would weaken the printed lemma and
  remove the orientation input consumed inside `yi`.

## What the passage costs, and one binder it does not need

`existsHypEmbeddedConeOff₂_of_yi` takes `yi` and `heGX` and nothing else.  In
particular it does **not** need `Independent`, which the earlier route through
`existsHypEmbeddedConeOff₂_of_zpowers` did: the trivial-intersection clause
`x ∈ ⟨h₀⟩ → x ∈ ⟨h₁⟩ → x = 1` follows from non-commensurability directly, since
`h₀ᵖ = x = h₁ᑫ` with both exponents nonzero contradicts it and either exponent
zero gives `x = 1` outright.  So the route through `yi` retires the independence
input rather than inheriting it, and `GGT.ElementaryOsinSNormal.IndependentOfNoCommonZpow`
is not on this path at all.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## The two statements -/

/-- **Hull's Lemma `nonelsub`.**  For every `k ≥ 1`, a non-elementary subgroup
contains `k` pairwise non-commensurable loxodromic elements whose elementary
closures are orientation-preserving.

The `k = 3` instance is load-bearing downstream: the orientation argument
inside `yi` needs three, because the sequences `123123…` and `321321…` have no
common subsequence of length two while `1212…` and `2121…` do.  The statement
nevertheless keeps Hull's printed all-`k` quantifier rather than baking in that
one consumer.

Non-commensurability is the conjugate form, `∀ c p q, c⁻¹fᵢᵖc ≠ f_jᑫ`, for the
reason in the module header.

**What proving this will cost, recorded here so it is not discovered late.**
The non-commensurability and WPD of Hull's `f_i = a b c_i` come from DGO's
Lemma 4.21, which applies only to words in the class `W`, and **(W1)** forbids
two consecutive `X`-letters.  Hull's `g` here is an arbitrary element of
`G = ⟨𝒜⟩`, so its spelling is a word of base letters of length `≥ 2` for all but
trivial `g`, and it is **not** a `W`-word.  DGO never meet this because their
Corollary 4.27 lets them enlarge the base by the letters they need --- at
`dgo1111.txt:2655`, *"By Corollary 4.27 we can assume that `t ∈ X` without loss
of generality"* --- after which `g` is a single letter and the word is Hull's own
`(a h)^N`.  So this statement's proof route runs through the same finite-
enlargement citation the relator lane needs, and loxodromy comes back down to
`Γ(G,𝒜)` by Hull's Lemma A1 (`GGT/HullYiAlphabetTransfer.lean`), which is
exactly the step his proof makes.

`YiSuitablePair` below does **not** pay this: there `g = a₁⋯a_{k-1}` is spelled
by letters of distinct peripheral factors, so the word has no `X`-letters at all
and (W1) holds vacuously.

The other input that route needs is Osin's theorem Hull cites as `subah` --- a
non-elementary subgroup contains a loxodromic element `h` together with some
`g ∉ E_G(h)` --- which is what supplies the `g` in the first place.  It is not in
this repository either. -/
def NonElSub : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {S : Subgroup G},
    ActsNonElementarily S (Cayley.base A.alphabet) →
      ∀ k : ℕ, 0 < k →
        ∃ f : Fin k → G, (∀ i : Fin k, f i ∈ S) ∧
          (∀ i : Fin k, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
          (∀ i j : Fin k, i ≠ j → ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
            c⁻¹ * f i ^ p * c ≠ f j ^ q) ∧
          ∀ i : Fin k,
            (GGT.Elementary.elementaryClosure (f i) : Set G) =
              GGT.Elementary.positiveElementaryClosure (f i)

/-- **The exact algebraic package `yi` extracts from `nonelsub`.**

Uniform coarse translation gives the finite-transversal conclusion of DGO
Lemma 6.5 (WPD is automatic from `A.acylindrical`), and Corollary 6.6 identifies
`E⁺(fᵢ)` with the centralizer of one positive power.  Composing that equality
with `nonelsub`'s `E(fᵢ) = E⁺(fᵢ)` clause produces the powers `aᵢ` used in
Hull's component-matching proof of `yi`. -/
theorem exists_nonElSub_centralizerPowers (hnon : NonElSub.{u})
    {G : Type u} [Group G] (A : HullGeneratingSet G) {S : Subgroup G}
    (hS : ActsNonElementarily S (Cayley.base A.alphabet))
    (hct : ElementaryClosureCoarseTranslation G (Cayley.base A.alphabet))
    (k : ℕ) (hk : 0 < k) :
    ∃ (f : Fin k → G) (r : Fin k → ℕ),
      (∀ i, f i ∈ S) ∧
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
      (∀ i j, i ≠ j → ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
        c⁻¹ * f i ^ p * c ≠ f j ^ q) ∧
      (∀ i, 0 < r i) ∧
      ∀ i, (elementaryClosure (f i) : Set G) =
        {c : G | Commute c (f i ^ (r i : ℤ))} := by
  obtain ⟨f, hfS, hflox, hfnc, hforient⟩ := hnon A hS k hk
  have hpow : ∀ i : Fin k, ∃ r : ℕ, 0 < r ∧
      positiveElementaryClosure (f i) =
        {c : G | Commute c (f i ^ (r : ℤ))} := by
    intro i
    have hwpd : GGT.IsWPDAt (f i) (Cayley.base A.alphabet) :=
      GGT.isWPDAt_of_isAcylindrical A.acylindrical (hflox i)
    have hfin : ElementaryClosureFiniteTransversal (f i) :=
      exists_finite_transversal_elementaryClosure_of_coarseTranslation
        (isIsometricAction_cayley A.alphabet) hwpd (hflox i) hct
    exact exists_positiveElementaryClosure_eq_centralizer_pow
      (isIsometricAction_cayley A.alphabet) (hflox i) hfin
  choose r hr hcentral using hpow
  exact ⟨f, r, hfS, hflox, hfnc, hr,
    fun i => (hforient i).trans (hcentral i)⟩

/-- **Hull's Lemma `yi`, in the suitable case.**  A suitable subgroup contains
two non-commensurable loxodromic elements whose elementary closures are cyclic.

Hull's conclusion is `E_G(hᵢ) = ⟨hᵢ⟩ × K_G(S)`; over a suitable `S` the finite
factor is trivial (`GGT/HullYiLoxRadical.lean`), and this is that instance.

**The input this one needs that nothing else does.**  Hull's proof fixes powers
`aᵢ = fᵢ^{nᵢ}` with `E_G(fᵢ) = C_G(aᵢ)`, and that condition is what makes the
connecting letter commute with each `aᵢ` and so land in `E(f₁) ∩ ⋯ ∩ E(f_k)`.
It is `E_G(fᵢ) = E_G⁺(fᵢ)` --- `nonelsub`'s fourth clause, now carried by
`NonElSub` --- composed with the last sentence
of Hull's Lemma `E(h)` (Dahmani--Guirardel--Osin, Lemma 6.5 and Corollary 6.6):
`E_G⁺(h) = C_G(h^r)` for some `r`.

That lemma's third characterisation of `E_G(h)`, `∃ k m ≠ 0, g⁻¹h^k g = h^m`, is
`GGT.elementaryClosure` **by construction**.  The equivalence with the
`h^{±n}` form and `E⁺(h) = C_G(h^r)` are now proved in `DGOCorollary66`, modulo
the finite-transversal conclusion of DGO Lemma 6.5.  Thus the remaining Yi
work is the production of a pairwise non-commensurable, orientation-pure
  detecting family and the geometric consecutive-component producer from
  Lemma 4.21(b).  The finite-family-to-`loxRadical` bridge is closed in
  `HullYiFiniteRadicalDetector`, the inverse-orientation contradiction in
  `HullYiCyclicOrientation`, and the connector propagation and final prefix
  calculation in `HullYiMatchedProductRigidity`; none is part of the residue. -/
def YiSuitablePair : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N →
      ∃ g : Bool → G, (∀ b : Bool, g b ∈ N) ∧
        (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
          (∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
            c⁻¹ * g false ^ p * c ≠ g true ^ q) ∧
            ∀ b : Bool, elementaryClosure (g b) = Subgroup.zpowers (g b)

/-- **Hull's Corollary `heGX` at a pair** (Dahmani--Guirardel--Osin's
Theorem 6.8): the elementary closures of finitely many pairwise
non-commensurable loxodromic WPD elements are hyperbolically embedded over the
prescribed alphabet.

Carried as a statement because its proof is Hull's Theorem `crit` — quasi-convex
and geometrically separated subgroups are hyperbolically embedded — together
with the verification that elementary closures satisfy both, which is
`coneoff-heavy-lane`'s B1 and B2.  The non-commensurability hypothesis is the
conjugate form for the reason in the module header: at the weak form the
conclusion is refuted by `not_isHyperbolicallyEmbedded_elementaryClosure_conj`.

**This is the pair instance, not the primary form.**  `GGT.HeGXSingle`, in the
`RelGenSet` vocabulary through `GGT.IsHypEmbeddedOf`, is the single-subgroup
statement and is the form of record; this one is its instance at `k = 2`, which
is what the two-subgroup cone-off consumes.  The bridge from the single form to
this one is owed by whichever of the two is discharged first. -/
def HeGXPair : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (g : Bool → G),
    (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) →
      (∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
        c⁻¹ * g false ^ p * c ≠ g true ^ q) →
        (coneOffFamily A.alphabet
          (fun b => elementaryClosure (g b))).IsHyperbolicallyEmbedded

/-! ## The passage to the Hull row -/

/-- The one ordered non-commensurability clause returned by `yi` is exactly
the pairwise predicate on a `Bool`-indexed family.  The reverse ordered pair is
obtained by conjugating the alleged equality back by the same element. -/
theorem pairwiseNonCommensurable_bool_of_notCommensurable
    {G : Type u} [Group G] {g : Bool → G}
    (hnc : ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
      c⁻¹ * g false ^ p * c ≠ g true ^ q) :
    PairwiseNonCommensurable g := by
  intro lam mu hne p q hp hq t
  cases lam <;> cases mu
  · exact (hne rfl).elim
  · simpa only [inv_inv] using hnc t⁻¹ p q hp hq
  · intro hbad
    apply hnc t q p hq hp
    calc
      t⁻¹ * g false ^ q * t =
          t⁻¹ * (t * g true ^ p * t⁻¹) * t := by rw [hbad]
      _ = g true ^ p := by group
  · exact (hne rfl).elim

/-- **Non-commensurable cyclic subgroups meet trivially.**  A common element is
`h₀ᵖ = h₁ᑫ`; if either exponent is zero the element is `1`, and if neither is,
non-commensurability at the trivial conjugator is contradicted. -/
theorem eq_one_of_mem_zpowers_of_notCommensurable {G : Type u} [Group G]
    {a b : G} (hnc : ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
      c⁻¹ * a ^ p * c ≠ b ^ q) {x : G} (hx0 : x ∈ Subgroup.zpowers a)
    (hx1 : x ∈ Subgroup.zpowers b) : x = 1 := by
  obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp hx0
  obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hx1
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [← hq, zpow_zero]
  · rcases eq_or_ne p 0 with rfl | hp0
    · rw [← hp, zpow_zero]
    · refine absurd ?_ (hnc 1 p q hp0 hq0)
      rw [inv_one, one_mul, mul_one, hp, ← hq]

/-- **`yi` and `heGX` close the Hull row.**

`ExistsHypEmbeddedConeOff₂` asks for two subgroups of `N` whose cone-off is
hyperbolically embedded, containing loxodromic elements, and meeting trivially.
Take the cyclic subgroups `yi` provides: containment is `Subgroup.zpowers_le`,
membership is `Subgroup.mem_zpowers`, the embedding is `heGX` read through
`E_G(hᵢ) = ⟨hᵢ⟩`, and the trivial intersection is non-commensurability.

**`GGT.ElementaryOsinSNormal.IndependentOfNoCommonZpow` is not consumed on this
route.**  The earlier passage, through `existsHypEmbeddedConeOff₂_of_zpowers`,
needed `Independent` to discharge the trivial-intersection clause via
`zpowers_disjoint_of_independent`.  Here that clause comes from
non-commensurability directly (`eq_one_of_mem_zpowers_of_notCommensurable`), so
independence is neither hypothesis nor input, and nothing on this path owes
it. -/
theorem existsHypEmbeddedConeOff₂_of_yi (hyi : YiSuitablePair.{u})
    (hheGX : HeGXPair.{u}) : ExistsHypEmbeddedConeOff₂.{u} := by
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hnc, hcyc⟩ := hyi A hN
  have hemb := hheGX A g hglox hnc
  have hfam : (fun b : Bool => elementaryClosure (g b))
      = fun b : Bool => Subgroup.zpowers (g b) := funext hcyc
  rw [hfam] at hemb
  refine ⟨fun b => Subgroup.zpowers (g b), ?_, hemb, g, ?_, hglox, ?_⟩
  · intro b
    exact Subgroup.zpowers_le.mpr (hgN b)
  · intro b
    exact Subgroup.mem_zpowers (g b)
  · intro x hx0 hx1
    exact eq_one_of_mem_zpowers_of_notCommensurable hnc hx0 hx1

end HullSC
end GroupApproximation
