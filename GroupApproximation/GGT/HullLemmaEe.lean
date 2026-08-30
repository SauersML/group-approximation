import GroupApproximation.GGT.HullEllipticity
import GroupApproximation.GGT.OsinTheorem54Family
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor
import GroupApproximation.GGT.ElementaryClosure

/-!
# Hull's Lemma `ee`: enlarging the alphabet to make prescribed elements elliptic

Hull, *Small cancellation in acylindrically hyperbolic groups* (arXiv:1308.4345),
Lemma `ee`:

> Let `{H_λ} ↪_h (G, X)` and let `a₁,…,a_m ∈ G`.  Then there exists `Y ⊇ X` such
> that (1) `{H_λ} ↪_h (G, Y)`, and (2) for each `i`, `a_i` is elliptic with
> respect to the action of `G` on `Γ(G, Y ⊔ ℋ)`.

This module states it, names the citations it rests on, and proves the assembly.
The one geometric step is isolated as `EeOneStep` and discharged elsewhere.

## Lemma `ee` is NOT Dahmani--Guirardel--Osin's Corollary 4.27

The two are easy to conflate and the conflation is costly, so it is recorded
here.  Corollary 4.27 --- carried in this repository as the unproved
`GGT.DGOCorollary427` --- says hyperbolic embeddedness is insensitive to a
**finite** change of relative generating set.  Hull cites it, as his Lemma
`finsymdif`, at exactly one step *inside* the proof below.  It cannot replace the
lemma, because the enlargement here is **infinite**: Hull adjoins the whole
elementary closure `E(a)`, not the element `a`.

And the infinite enlargement is necessary, not incidental.  Putting `a` itself
into the base gives clause (1) from 4.27 immediately, and does **not** give
clause (2): membership in the generating set does not make an element elliptic.
Take `G = ℤ = ⟨a⟩` with the empty family and `X = {a, a⁻¹}`; then `Γ(G, X)` is a
line, `a` lies in `X`, and `a` translates the line, so it is loxodromic.  Clause
(2) is bought by adjoining `E(a)`, and by nothing cheaper.

## Uniformity in Proposition 4.14 is NOT needed

Hull's proof reaches its bound through his Lemma `C`, which is Dahmani--
Guirardel--Osin's Proposition 4.14, and applies it to a cycle every edge of which
is a side --- so the side count grows with the radius.  That is the regime in
which `GGT/HullYiLemmaC.lean` records that the uniform constant is out of reach
here, and it makes the lemma look blocked behind the hardest open leaf in this
area.  It is not.

**The bound's only consumer is a finiteness claim.**  It is used once, to define
`F_n = {g ∈ E(a) : d̂(1,g) ≤ C(n+1)}` and conclude that `F_n` is *finite* from
local finiteness of `E(a)`.  Linearity in `n` is never read.  Any radius that is
finite for each `n` does the same work, and
`OsinComponents.exists_isolatedComponentBound_nGon` supplies one --- radius
`(N+1) · 25(δ+b+1) · (N+2)`, quadratic in the side count and finite at every `n`.
So Lemma `ee` is independent of uniform 4.14, and `EeOneStep` below is stated so
that its discharge may use the non-uniform bound.

A second economy in the same place: instantiating that bound at `b = 1` makes the
per-side quasi-geodesic condition `(j − i)/μ − b ≤ d` vacuous whenever
`j − i ≤ 1`, so "every edge is its own side" is automatically a quasi-geodesic
polygon and no non-triviality hypothesis on letters is needed --- which matters,
since `ℋ` carries identity loops by Dahmani--Guirardel--Osin's own convention.

## What is assumed, and why each is the smallest form

* **`OsinTheorem54Fam`** is Hull's Theorem `Ahyp`, already in the repository.
* **`HeGXSingle`** is Hull's Corollary `heGX` at one element, stated here.  It
  takes acylindricity rather than WPD, which absorbs the step *"since the action
  is acylindrical, all loxodromic elements satisfy WPD"* that the repository has
  no theorem for.
* **`Elementary.EllipticOrEscaping`** is the **only** part of Bowditch's
  dichotomy still missing.  This deserves the detail, because the obvious reading
  of the repository is that Bowditch is already available and it is not, in this
  shape.  What is proved is
  `escapingIsLoxodromic_cayley_of_acylindrical` --- *escaping* implies
  loxodromic, at any hyperbolic acylindrical alphabet.  Hull needs *not elliptic*
  implies loxodromic, and an unbounded orbit need not escape: boundedness fails
  on a subsequence, escape is a statement about the limit.  Closing that is
  genuinely part of Bowditch's theorem.  So the residue carried is exactly
  `elliptic or escaping` and no more, and
  `isElliptic_or_isLoxodromic_of_acylindrical` below combines it with the proved
  half to give Hull's Lemma `loxorell`.  Carrying the whole dichotomy instead
  would re-cite work this repository has already done.
* **`EeOneStep`** is the geometric core, and the only clause not assembled here.

`GGT.DGOCorollary427` is deliberately **not** a hypothesis of this module: it is
consumed inside `EeOneStep`, and naming it here would suggest the assembly reads
it when the assembly does not.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## 1.  The missing half of Bowditch's dichotomy -/

namespace Elementary

/-- **Every element is elliptic or escaping.**

The half of Bowditch's dichotomy (Osin, Theorem 1.1) that this repository does
not prove.  Its sibling `EscapingIsLoxodromic` is the half that *is* proved, at
any hyperbolic acylindrical alphabet, by
`HullSCUnionGeometry.escapingIsLoxodromic_cayley_of_acylindrical`.

Stated as `elliptic or escaping` rather than as `elliptic or loxodromic` because
that is the smaller statement: it is implied by the dichotomy, and combined with
the proved half it returns the dichotomy.  A citation weaker than the
printed theorem is a safer citation. -/
def EllipticOrEscaping (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ c : G, IsElliptic c x ∨ IsEscaping c x

end Elementary

/-- **Hull's Lemma `loxorell`**: under an acylindrical action on a hyperbolic
Cayley graph every element is elliptic or loxodromic.

Half proved, half cited, and the split is the point: `EscapingIsLoxodromic` is
already a theorem here, so the citation is reduced to `EllipticOrEscaping`. -/
theorem isElliptic_or_isLoxodromic_of_acylindrical {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (hacyl : IsAcylindrical G (Cayley A))
    (hdich : Elementary.EllipticOrEscaping G (Cayley.base A)) (c : G) :
    IsElliptic c (Cayley.base A) ∨ IsLoxodromic c (Cayley.base A) := by
  rcases hdich c with hell | hesc
  · exact Or.inl hell
  · exact Or.inr
      (HullSCUnionGeometry.escapingIsLoxodromic_cayley_of_acylindrical A hδ hacyl
        c hesc)

/-! ## 2.  The two statements this module assumes -/

/-- **Hull's Corollary `heGX` at a single element** (Dahmani--Guirardel--Osin,
Theorem 6.8): the elementary closure of a loxodromic element is hyperbolically
embedded over the prescribed alphabet.

This is the `RelGenSet` single form; `HullSC.HeGXPair` is the same citation at a
pair, over a `HullGeneratingSet` cone-off.  The two are instances of one
statement and whoever discharges either owes the bridge between them --- the pair
form is this one read at `k = 2`.

Acylindricity rather than WPD: Hull's proof reaches `heGX` through *"since the
action is acylindrical, all loxodromic elements satisfy WPD"*, and this
repository has no theorem for that implication.  Taking acylindricity as the
hypothesis absorbs the step instead of leaving it as a second unnamed debt. -/
def HeGXSingle : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → IsAcylindrical G (Cayley D.alphabet) →
      ∀ a : G, IsLoxodromic a (Cayley.base D.alphabet) →
        IsHypEmbeddedOf G D.alphabet.carrier (elementaryClosure a)

/-- **The geometric core of Lemma `ee`**: a subgroup hyperbolically embedded over
the whole alphabet may be moved into the base without disturbing the family.

This is Hull's claim *"we claim that in fact `{H_λ} ↪_h (G, Y₀ ⊔ E_G(a))`"*, and
it is the whole of what his proof of Lemma `ee` actually argues.  Clause (a) is
free, the two alphabets having the same carrier; clause (b) is the isolated
component estimate, `F_n`, and Corollary 4.27, and is discharged separately.

Stated over an arbitrary hyperbolically embedded `E` rather than over
`elementaryClosure a`, because the argument never inspects which subgroup it is
--- it reads only that `E` is hyperbolically embedded over the same alphabet, so
that its own relative metric is locally finite. -/
def EeOneStep : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∀ E : Subgroup G, IsHypEmbeddedOf G D.alphabet.carrier E →
        ∃ D' : RelGenSet G Λ, D'.base = D.base ∪ (E : Set G) ∧
          D'.fam = D.fam ∧ D'.IsHyperbolicallyEmbedded

/-- **Hull's Lemma `ee`.**  The enlargement is monotone in the base, fixes the
family, keeps the family hyperbolically embedded, and makes every prescribed
element elliptic.

The prescribed elements are a `List` rather than a `Fin m → G`, because the proof
is an induction along them and `List.rec` is that induction. -/
def HullLemmaEe : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) [Finite Λ] (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∀ as : List G, ∃ D' : RelGenSet G Λ, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
        D'.IsHyperbolicallyEmbedded ∧
          ∀ x ∈ as, IsElliptic x (Cayley.base D'.alphabet)

/-! ## 3.  Alphabets grow with their bases -/

section Alphabet

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The base sits inside the alphabet.** -/
theorem base_subset_alphabet_carrier (D : RelGenSet G Λ) :
    D.base ⊆ D.alphabet.carrier := by
  intro x hx
  show x ∈ D.base ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)
  exact Set.mem_union_left _ hx

/-- **Enlarging the base enlarges the alphabet**, the family being fixed.  This
is what carries ellipticity forward through the induction: an element made
elliptic at one stage is still elliptic at every later one, by
`HullSC.isElliptic_base_of_subset`. -/
theorem alphabet_carrier_mono {D D' : RelGenSet G Λ} (hbase : D.base ⊆ D'.base)
    (hfam : D'.fam = D.fam) : D.alphabet.carrier ⊆ D'.alphabet.carrier := by
  intro x hx
  have hx' : x ∈ D.base ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G) := hx
  show x ∈ D'.base ∪ ⋃ lam : Λ, ((D'.fam lam : Subgroup G) : Set G)
  rcases hx' with hb | hf
  · exact Set.mem_union_left _ (hbase hb)
  · refine Set.mem_union_right _ ?_
    rw [hfam]
    exact hf

end Alphabet

/-! ## 4.  One prescribed element -/

/-- **Lemma `ee` at a single element.**

The three cases of Hull's proof, in order.  Theorem 5.4 supplies an enlargement
on which the action is acylindrical; the dichotomy splits on the element there;
if it is elliptic that enlargement already works, and if it is loxodromic then
`heGX` puts its elementary closure into the alphabet and `EeOneStep` moves the
closure into the base, after which the element is elliptic because every one of
its powers has become a letter. -/
theorem ee_one (h54 : OsinEnlargement.OsinTheorem54Fam.{u, w}) (hheGX : HeGXSingle.{u, w})
    (hone : EeOneStep.{u, w})
    (hdich : ∀ (G : Type u) [Group G] (A : Alphabet G),
      Elementary.EllipticOrEscaping G (Cayley.base A))
    (G : Type u) [Group G] (Λ : Type w) [Finite Λ] (D : RelGenSet G Λ)
    (hD : D.IsHyperbolicallyEmbedded) (a : G) :
    ∃ D' : RelGenSet G Λ, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      D'.IsHyperbolicallyEmbedded ∧ IsElliptic a (Cayley.base D'.alphabet) := by
  obtain ⟨D₀, hsub₀, hfam₀, hemb₀, hacy₀⟩ := h54 G Λ D hD
  obtain ⟨δ, hδ⟩ := hemb₀.hyperbolic
  rcases isElliptic_or_isLoxodromic_of_acylindrical D₀.alphabet hδ hacy₀
    (hdich G D₀.alphabet) a with hell | hlox
  · exact ⟨D₀, hsub₀, hfam₀, hemb₀, hell⟩
  · have hE : IsHypEmbeddedOf G D₀.alphabet.carrier (elementaryClosure a) :=
      hheGX G Λ D₀ hemb₀ hacy₀ a hlox
    obtain ⟨D₁, hbase₁, hfam₁, hemb₁⟩ := hone G Λ D₀ hemb₀ (elementaryClosure a) hE
    have hsub₁ : D₀.base ⊆ D₁.base := by
      rw [hbase₁]
      exact Set.subset_union_left
    have hEsub : ((elementaryClosure a : Subgroup G) : Set G)
        ⊆ D₁.alphabet.carrier := by
      refine Set.Subset.trans ?_ (base_subset_alphabet_carrier D₁)
      rw [hbase₁]
      exact Set.subset_union_right
    refine ⟨D₁, Set.Subset.trans hsub₀ hsub₁, ?_, hemb₁, ?_⟩
    · rw [hfam₁, hfam₀]
    · exact isElliptic_base_of_mem_subgroup hEsub (self_mem_elementaryClosure a)

/-! ## 5.  The induction -/

/-- **Hull's Lemma `ee`, assembled.**

The induction is along the list of prescribed elements.  At each step `ee_one`
supplies an enlargement making the head elliptic, and the elements handled
earlier stay elliptic because the alphabet only grew --- which is
`HullSC.isElliptic_base_of_subset`, the transfer direction opposite to Hull's
Lemma A.1, and is exactly the sentence his proof opens with. -/
theorem hullLemmaEe_of_inputs (h54 : OsinEnlargement.OsinTheorem54Fam.{u, w})
    (hheGX : HeGXSingle.{u, w}) (hone : EeOneStep.{u, w})
    (hdich : ∀ (G : Type u) [Group G] (A : Alphabet G),
      Elementary.EllipticOrEscaping G (Cayley.base A)) :
    HullLemmaEe.{u, w} := by
  intro G _instG Λ _finΛ D hD as
  induction as generalizing D hD with
  | nil =>
      exact ⟨D, Set.Subset.rfl, rfl, hD, by simp⟩
  | cons a t ih =>
      obtain ⟨D₁, hsub₁, hfam₁, hemb₁, hell₁⟩ :=
        ee_one h54 hheGX hone hdich G Λ D hD a
      obtain ⟨D₂, hsub₂, hfam₂, hemb₂, hell₂⟩ := ih D₁ hemb₁
      have hcar : D₁.alphabet.carrier ⊆ D₂.alphabet.carrier :=
        alphabet_carrier_mono hsub₂ hfam₂
      refine ⟨D₂, Set.Subset.trans hsub₁ hsub₂, ?_, hemb₂, ?_⟩
      · rw [hfam₂, hfam₁]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact isElliptic_base_of_subset hcar hell₁
        · exact hell₂ x hxt

end GGT
end GroupApproximation
