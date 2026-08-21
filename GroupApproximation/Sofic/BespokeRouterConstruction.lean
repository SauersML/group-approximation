import GroupApproximation.Sofic.SmallCancellationRouter
import GroupApproximation.Sofic.OsinRelativeSmallCancellation
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Coprod.Basic

/-!
# The bespoke router construction, parametrically

`Sofic.SmallCancellationRouter` freezes the *output* of the routing lemma as
`RoutingLemmaData E N s B`: a common quotient of a source `E` and a Kazhdan
partner `B` in which the designated normal subgroup `N` fills everything and a
protected element `s` survives.  This module builds the *input* side — the
concrete quotient the routing lemma is meant to produce — over an arbitrary
relator family, so that the coordinator's word design has a typed target to be
designed against.

## The shape

The ambient group is the free product of two factors, indexed by `Bool`: a
**source factor** `S` at `false` and the **partner** `B` at `true`
(`factor`, `Ambient`).  The source group `E` of the interface reaches the free
product through a homomorphism `pre : E →* S`; taking `S = E` and `pre` the
identity recovers the literal "free product of the source and the partner", and
the extra parameter costs nothing.  It is not idle: §5 below proves that it is
where *all* of the collapsing has to happen.

A `RouterRelatorDesign` bundles the obligations an explicit word family must
meet.  Its fields are statements about the family, never conclusions of the
routing lemma in disguise; the conclusions — `defect_top`, `generates`,
`route_surjective`, `partner_surjective`, finite presentation, torsion-freeness
and protected survival — are *derived* from them in §4, each one a theorem.

Two of the derivations consume the relative Greendlinger gate, and they consume
it the way the library consumes gates: as an explicit hypothesis
(`RelativeGreendlingerGate`), never as an axiom, so that
`Sofic.GreendlingerRelativeTransfer` can be plugged into a single named site
when it lands.  Everything else is unconditional.

## The design fields, and why each is honest

* `pre`, `relators`, `relators_finite`, `relators_cyclicallyReduced`,
  `relators_long`, `metric` — the family itself and the small-cancellation
  hypotheses.  `relators` is understood to be already symmetrized (closed under
  cyclic rotation and inversion), the convention `OsinSmallCancellation.IsPiece`
  is stated for.
* `basisOne`, `basisTwo`, and their membership in `N` — the designated pair
  inside the defect, in practice the free basis
  `ExplicitSuitableDefect.defectOne`, `defectTwo`.
* `card`, `gen`, `gen_closure` — a finite enumeration of a generating set of
  the ambient free product.
* `sourceCoverage`, `partnerCoverage` — the per-generator coverage, in
  **triangular** form: the relator for the `n`-th generator writes it as a word
  in the designated pair (respectively in the partner factor) together with the
  generators already covered.  Triangularity is what makes the field
  dischargeable rather than circular: a flat "every generator is a word in the
  designated pair" would already be `generates`, and a version whose
  conjugators range over the whole ambient group would be unusable, since the
  conjugators' own images are exactly what is being computed.  The induction
  that unwinds it is `gen_mem_coverTarget`.
* `protected_survives` — `s` is not killed by the first-stage map `pre`.  This
  is a statement about `pre`, not about the relator family; the relator family's
  half of protected survival is the factor-embedding clause, which is derived.

## Two findings the scaffold makes visible

**(1) The whole-syllable metric condition alone does not imply the Greendlinger
length bound.**  `OsinRelativeSmallCancellation` leaves
`MetricSmallCancellation R (1/6) → GreendlingerLengthBound R` open and records
that its pieces are whole syllables where Lyndon--Schupp's are fragments,
"which makes the hypothesis stronger than the classical one".  It makes it
*weaker*, and the implication as stated is false.  Take `S = ⟨e⟩ ≅ ℤ`,
`B = ⟨b ∣ b²⟩ ≅ ℤ/2` and the symmetrized family of the single relator `e·b⁻¹`,
namely `{e·b⁻¹, b⁻¹·e, b·e⁻¹, e⁻¹·b}`.  No two distinct members share a first
syllable, so the only piece is the empty word and
`MetricSmallCancellation R (1/6)` holds; every member is cyclically reduced,
with `wlen = 2`.  But `b⁻¹ = b`, so `(e·b⁻¹)·(b⁻¹·e) = e·b⁻²·e = e²`, whence
`of (e²) ∈ relatorSubgroup R` while `sylLength (of (e²)) = 1`: the length bound
would need a relator with `wlen < 2`, and there is none.  Classically this
family is *not* `C'(1/6)`: over a free product any two symmetrized relators
whose first syllables lie in the same factor share **every** element of that
factor as a length-one fragment piece, so classical `C'(1/6)` forces
`wlen r > 6` outright.  That is why the design carries `relators_long`
(`7 ≤ wlen r`), which is free for a Rips-style family and kills the
counterexample; the gate that W1-relative proves must carry it, or an
equivalent fragment-aware piece notion, as a hypothesis.

**(2) The free-product small-cancellation stage never collapses the source
factor.**  `defect_eq_top_of_lengthBound`: as soon as the Greendlinger length
bound holds for the design's family — which is precisely what the gate is for —
the source factor `S` embeds in the routed quotient
(`factorMap_injective_of_cyclicallyReduced`), while `defect_top` forces it to
surject; so `routeOf` is an isomorphism `S ≃* Routed` and `N.map pre = ⊤`
already.  In other words a single `C'(1/6)` quotient of `S ∗ B` is never a
*proper* common quotient: the whole saturation `defect_top` must be achieved by
`pre`, before the free product is formed, and the small-cancellation stage can
only supply the partner's surjection (hence property (T)) and torsion-freeness.
A design that takes `S = E` and `pre = id` is therefore satisfiable only when
`E` is already the answer.  This is proved, not conjectured, and it is the
reason `pre` is a parameter.
-/

namespace GroupApproximation
namespace BespokeRouter

open Monoid Monoid.CoprodI OsinSmallCancellation

/-! ## 0.  A pair-injectivity lemma

The interface's protected-set obligation is injectivity on the two-element set
`{1, s}`, which is one implication away from nontriviality of the image. -/

/-- Injectivity on `{1, s}` is exactly the statement that `s` is not killed. -/
theorem injOn_pair {G H : Type} [Group G] [Group H] {f : G →* H} {s : G}
    (h : f s = 1 → s = 1) : Set.InjOn f ({1, s} : Set G) := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · rfl
    · exact (h (by rw [← hxy, map_one])).symm
  · rcases hy with rfl | rfl
    · exact h (by rw [hxy, map_one])
    · rfl

/-! ## 1.  The two-factor free product -/

/-- The two factors of the router's ambient free product: the source factor at
`false`, the Kazhdan partner at `true`. -/
def factor (S B : Type) : Bool → Type := fun b => cond b B S

theorem factor_false (S B : Type) : factor S B false = S := rfl

theorem factor_true (S B : Type) : factor S B true = B := rfl

instance instGroupFactor (S B : Type) [Group S] [Group B] :
    ∀ b : Bool, Group (factor S B b)
  | false => ‹Group S›
  | true => ‹Group B›

instance instDecidableEqFactor (S B : Type) [DecidableEq S] [DecidableEq B] :
    ∀ b : Bool, DecidableEq (factor S B b)
  | false => ‹DecidableEq S›
  | true => ‹DecidableEq B›

/-- **The router's ambient group**: the free product of the source factor and
the partner, as an indexed coproduct over `Bool`, which is the shape
`OsinRelativeSmallCancellation`'s word combinatorics is stated for. -/
abbrev Ambient (S B : Type) [Group S] [Group B] : Type := CoprodI (factor S B)

/-- The source factor's inclusion into the ambient free product. -/
def srcOf (S B : Type) [Group S] [Group B] : S →* Ambient S B :=
  CoprodI.of (M := factor S B) (i := false)

/-- The partner's inclusion into the ambient free product. -/
def parOf (S B : Type) [Group S] [Group B] : B →* Ambient S B :=
  CoprodI.of (M := factor S B) (i := true)

/-- The two factor inclusions into Mathlib's *binary* coproduct. -/
def toCoprodFactor (S B : Type) [Group S] [Group B] :
    ∀ b : Bool, factor S B b →* Monoid.Coprod S B
  | false => Monoid.Coprod.inl
  | true => Monoid.Coprod.inr

/-- **The indexed ambient is the binary coproduct.**  Mathlib's
finite-presentation instance for free products is stated for `Monoid.Coprod`,
and `Mathlib.GroupTheory.Coprod.Basic` lists this comparison in its own TODO
list; it is two applications of the two universal properties. -/
def coprodEquiv (S B : Type) [Group S] [Group B] :
    Ambient S B ≃* Monoid.Coprod S B :=
  MonoidHom.toMulEquiv (CoprodI.lift (toCoprodFactor S B))
    (Monoid.Coprod.lift (srcOf S B) (parOf S B))
    (CoprodI.ext_hom _ _ (by
      intro b
      rw [MonoidHom.comp_assoc, CoprodI.lift_comp_of, MonoidHom.id_comp]
      cases b <;> rfl))
    (Monoid.Coprod.hom_ext
      (by
        rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl, MonoidHom.id_comp]
        exact CoprodI.lift_comp_of (toCoprodFactor S B) false)
      (by
        rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr, MonoidHom.id_comp]
        exact CoprodI.lift_comp_of (toCoprodFactor S B) true))

/-- **The ambient free product of two finitely presented groups is finitely
presented**, by transport along `coprodEquiv`. -/
instance instAmbientFinitelyPresented (S B : Type) [Group S] [Group B]
    [Group.IsFinitelyPresented S] [Group.IsFinitelyPresented B] :
    Group.IsFinitelyPresented (Ambient S B) :=
  Group.IsFinitelyPresented.equiv (coprodEquiv S B).symm

/-- Torsion-freeness of the two factors, as the family the free-product torsion
theorem consumes. -/
theorem factor_isPowerTorsionFree {S B : Type} [Group S] [Group B]
    (hS : IsPowerTorsionFree S) (hB : IsPowerTorsionFree B) :
    ∀ b : Bool, IsPowerTorsionFree (factor S B b)
  | false => hS
  | true => hB

/-! ## 2.  The routed quotient, and the triangular coverage machinery -/

section Relators

variable {S B : Type} [Group S] [Group B] [DecidableEq S] [DecidableEq B]

/-- **The routed quotient**: the ambient free product modulo the normal closure
of the relator family. -/
abbrev RouterQuotient (R : Set (Word (factor S B))) : Type :=
  Ambient S B ⧸ relatorSubgroup R

/-- The routing map out of the source factor. -/
def routeOf (R : Set (Word (factor S B))) : S →* RouterQuotient R :=
  factorMap (relatorSubgroup R) false

/-- The map out of the partner factor. -/
def partnerOf (R : Set (Word (factor S B))) : B →* RouterQuotient R :=
  factorMap (relatorSubgroup R) true

omit [DecidableEq S] [DecidableEq B] in
/-- Every relator lies in the subgroup it presents. -/
theorem prod_mem_relatorSubgroup {R : Set (Word (factor S B))}
    {r : Word (factor S B)} (hr : r ∈ R) : Word.prod r ∈ relatorSubgroup R :=
  Subgroup.subset_normalClosure ⟨r, hr, rfl⟩

omit [DecidableEq S] [DecidableEq B] in
/-- A relator of the shape `g · w⁻¹` identifies `g` with `w` in the quotient.
This is the only way the coverage fields are ever used. -/
theorem mk_eq_of_coverage {R : Set (Word (factor S B))} {g w : Ambient S B}
    {r : Word (factor S B)} (hr : r ∈ R) (h : Word.prod r = g * w⁻¹) :
    QuotientGroup.mk' (relatorSubgroup R) g =
      QuotientGroup.mk' (relatorSubgroup R) w := by
  have hmem : g * w⁻¹ ∈ relatorSubgroup R := by
    rw [← h]
    exact prod_mem_relatorSubgroup hr
  have h1 : QuotientGroup.mk' (relatorSubgroup R) (g * w⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

/-- **The triangular coverage shape.**  For each enumerated generator of the
ambient free product the family contains a relator writing that generator as a
word in `base` together with the generators *before* it.  This is the shape a
Rips-style interleaved word design produces, and the ordering is what makes the
obligation dischargeable: the conjugators used at stage `n` have already been
computed at earlier stages. -/
def TriangularCoverage (R : Set (Word (factor S B))) (base : Set (Ambient S B))
    {k : ℕ} (gen : Fin k → Ambient S B) : Prop :=
  ∀ n : Fin k, ∃ r ∈ R, ∃ w ∈ Subgroup.closure (base ∪ gen '' {m | m < n}),
    Word.prod r = gen n * w⁻¹

/-- The ambient elements whose image in the routed quotient lies in the
subgroup generated by the image of `base`.  Working with this subgroup instead
of the image keeps the coverage induction inside `Subgroup` membership. -/
def coverTarget (R : Set (Word (factor S B))) (base : Set (Ambient S B)) :
    Subgroup (Ambient S B) :=
  (Subgroup.closure (QuotientGroup.mk' (relatorSubgroup R) '' base)).comap
    (QuotientGroup.mk' (relatorSubgroup R))

omit [DecidableEq S] [DecidableEq B] in
theorem mem_coverTarget_of_mem_base {R : Set (Word (factor S B))}
    {base : Set (Ambient S B)} {x : Ambient S B} (hx : x ∈ base) :
    x ∈ coverTarget R base :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

omit [DecidableEq S] [DecidableEq B] in
/-- **The coverage induction.**  Every enumerated generator lands in the
subgroup generated by the images of `base`, by strong induction along the
triangular order. -/
theorem gen_mem_coverTarget {R : Set (Word (factor S B))}
    {base : Set (Ambient S B)} {k : ℕ} {gen : Fin k → Ambient S B}
    (hcov : TriangularCoverage R base gen) (n : Fin k) :
    gen n ∈ coverTarget R base := by
  have key : ∀ m : ℕ, ∀ p : Fin k, p.val = m → gen p ∈ coverTarget R base := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro p hp
      obtain ⟨r, hr, w, hw, hprod⟩ := hcov p
      have hwmem : w ∈ coverTarget R base := by
        refine (Subgroup.closure_le _).mpr ?_ hw
        rintro x (hx | ⟨q, hq, rfl⟩)
        · exact mem_coverTarget_of_mem_base hx
        · exact ih q.val (by rw [← hp]; exact hq) q rfl
      have hq : QuotientGroup.mk' (relatorSubgroup R) (gen p) ∈
          Subgroup.closure (QuotientGroup.mk' (relatorSubgroup R) '' base) := by
        rw [mk_eq_of_coverage hr hprod]
        exact hwmem
      exact hq
  exact key n.val n rfl

omit [DecidableEq S] [DecidableEq B] in
/-- **The coverage conclusion.**  If the enumerated generators generate the
ambient free product, then the images of `base` generate the routed quotient. -/
theorem closure_image_eq_top_of_triangular {R : Set (Word (factor S B))}
    {base : Set (Ambient S B)} {k : ℕ} {gen : Fin k → Ambient S B}
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hcov : TriangularCoverage R base gen) :
    Subgroup.closure (QuotientGroup.mk' (relatorSubgroup R) '' base) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (relatorSubgroup R) y
  have hx : x ∈ Subgroup.closure (Set.range gen) := by
    rw [hgen]
    exact Subgroup.mem_top x
  have hle : Subgroup.closure (Set.range gen) ≤ coverTarget R base := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    exact gen_mem_coverTarget hcov n
  exact hle hx

/-! ## 3.  The gate, as an explicit hypothesis

The one thing the construction cannot supply for itself: the relative
Greendlinger transfer over `Monoid.CoprodI` syllables.  It is consumed exactly
the way `SmallCancellationRouter.GreendlingerGate` is consumed on the
free-group side — as a hypothesis, never as an axiom — so that
`Sofic.GreendlingerRelativeTransfer` slots into one named site.

The length hypothesis `7 ≤ wlen r` is not decoration: without it the
implication is false, by the two-syllable counterexample in the module
docstring. -/

/-- **The relative Greendlinger gate**, in the shape the router construction
consumes: a long, cyclically reduced, whole-syllable `C'(1/6)` family satisfies
the length bound and the torsion classification. -/
def RelativeGreendlingerGate (S B : Type) [Group S] [Group B]
    [DecidableEq S] [DecidableEq B] : Prop :=
  ∀ R : Set (Word (factor S B)),
    (∀ r ∈ R, IsCyclicallyReduced r) →
    (∀ r ∈ R, 7 ≤ wlen r) →
    MetricSmallCancellation R (1 / 6) →
    GreendlingerLengthBound R ∧ TorsionIntoFactors (relatorSubgroup R)

end Relators

/-! ## 4.  The design, and the derivations -/

/-- **The word-design obligations.**  Everything the coordinator's explicit
relator family has to satisfy, and nothing that is a conclusion of the routing
lemma: see the module docstring for the field-by-field justification.  The
family `relators` is understood to be symmetrized, the convention
`OsinSmallCancellation.IsPiece` is stated for. -/
structure RouterRelatorDesign (E : Type) [Group E] (N : Subgroup E) (s : E)
    (S B : Type) [Group S] [Group B] [DecidableEq S] [DecidableEq B] where
  /-- The first-stage map: the source group into the source factor. -/
  pre : E →* S
  /-- The symmetrized relator family, as syllable words. -/
  relators : Set (Word (factor S B))
  /-- Finitely many relators — the finite-presentation obligation. -/
  relators_finite : relators.Finite
  /-- Every relator is cyclically reduced: its first and last syllables lie in
  different factors. -/
  relators_cyclicallyReduced : ∀ r ∈ relators, IsCyclicallyReduced r
  /-- Every relator has at least seven syllables.  Classical `C'(1/6)` over a
  free product forces this, and the whole-syllable condition does not; see the
  module docstring. -/
  relators_long : ∀ r ∈ relators, 7 ≤ wlen r
  /-- The whole-syllable metric small-cancellation condition. -/
  metric : MetricSmallCancellation relators (1 / 6)
  /-- The first designated element of the defect. -/
  basisOne : E
  /-- The second designated element of the defect. -/
  basisTwo : E
  /-- The first designated element lies in the designated normal subgroup. -/
  basisOne_mem : basisOne ∈ N
  /-- The second designated element lies in the designated normal subgroup. -/
  basisTwo_mem : basisTwo ∈ N
  /-- The number of enumerated ambient generators. -/
  card : ℕ
  /-- The enumerated ambient generators. -/
  gen : Fin card → Ambient S B
  /-- They generate the ambient free product. -/
  gen_closure : Subgroup.closure (Set.range gen) = ⊤
  /-- **Source coverage**: triangularly, each generator is a relator away from
  a word in the two designated defect elements. -/
  sourceCoverage : TriangularCoverage relators
    ({srcOf S B (pre basisOne), srcOf S B (pre basisTwo)} : Set (Ambient S B))
    gen
  /-- **Partner coverage**: triangularly, each generator is a relator away from
  a word in the partner factor. -/
  partnerCoverage : TriangularCoverage relators (Set.range (parOf S B)) gen
  /-- The protected element survives the first stage. -/
  protected_survives : s ≠ 1 → pre s ≠ 1

namespace RouterRelatorDesign

variable {E : Type} [Group E] {N : Subgroup E} {s : E}
    {S B : Type} [Group S] [Group B] [DecidableEq S] [DecidableEq B]
    (D : RouterRelatorDesign E N s S B)

/-- The routed quotient of a design. -/
abbrev Routed : Type := RouterQuotient D.relators

/-- The routing map of a design: the source group into the routed quotient,
through the first stage and then the source factor. -/
def route : E →* D.Routed := (routeOf D.relators).comp D.pre

/-- The partner map of a design. -/
def partner : B →* D.Routed := partnerOf D.relators

/-- The first produced generator of the routed quotient. -/
def genOne : D.Routed := D.route D.basisOne

/-- The second produced generator of the routed quotient. -/
def genTwo : D.Routed := D.route D.basisTwo

/-- The produced generators are the classes of the designated defect elements
read inside the source factor. -/
theorem genOne_eq : D.genOne =
    QuotientGroup.mk' (relatorSubgroup D.relators)
      (srcOf S B (D.pre D.basisOne)) := rfl

theorem genTwo_eq : D.genTwo =
    QuotientGroup.mk' (relatorSubgroup D.relators)
      (srcOf S B (D.pre D.basisTwo)) := rfl

/-- The partner map is the class of the partner factor's inclusion. -/
theorem partner_apply (y : B) : D.partner y =
    QuotientGroup.mk' (relatorSubgroup D.relators) (parOf S B y) := rfl

/-- **Two-generation, derived.**  The images of the two designated defect
elements generate the routed quotient: this is the source coverage, unwound. -/
theorem generates :
    Subgroup.closure ({D.genOne, D.genTwo} : Set D.Routed) = ⊤ := by
  have h := closure_image_eq_top_of_triangular D.gen_closure D.sourceCoverage
  rw [Set.image_insert_eq, Set.image_singleton] at h
  rw [D.genOne_eq, D.genTwo_eq]
  exact h

/-- **The routing map is onto, derived.**  Both produced generators are images
of source elements, and they generate. -/
theorem route_surjective : Function.Surjective D.route := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← D.generates, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨D.basisOne, rfl⟩
  · exact ⟨D.basisTwo, rfl⟩

/-- The source factor itself surjects onto the routed quotient. -/
theorem routeOf_surjective : Function.Surjective (routeOf D.relators) := by
  intro y
  obtain ⟨x, hx⟩ := D.route_surjective y
  exact ⟨D.pre x, hx⟩

/-- **The partner map is onto, derived.**  This is the partner coverage,
unwound. -/
theorem partner_surjective : Function.Surjective D.partner := by
  have h := closure_image_eq_top_of_triangular D.gen_closure D.partnerCoverage
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← h, Subgroup.closure_le]
  rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
  exact ⟨y, (D.partner_apply y).symm⟩

/-- **Saturation, derived.**  The designated normal subgroup fills the routed
quotient, because the two elements that generate it are images of elements of
`N`.  This is the field the interface calls `defect_top`. -/
theorem defect_top : N.map D.route = ⊤ := by
  rw [eq_top_iff, ← D.generates, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨D.basisOne, D.basisOne_mem, rfl⟩
  · exact ⟨D.basisTwo, D.basisTwo_mem, rfl⟩

/-- The relator subgroup is the normal closure of a finite set. -/
theorem finitelyNormallyGenerated :
    (relatorSubgroup D.relators).IsFinitelyNormallyGenerated :=
  ⟨Word.prod '' D.relators, D.relators_finite.image _, rfl⟩

/-- **Finite presentation, derived.**  Finitely many relators over finitely
presented factors: Mathlib's free-product instance through `coprodEquiv`, then
its quotient lemma. -/
theorem finitelyPresented [Group.IsFinitelyPresented S]
    [Group.IsFinitelyPresented B] : Group.IsFinitelyPresented D.Routed :=
  Group.IsFinitelyPresented.quotient _ D.finitelyNormallyGenerated

/-- **Torsion-freeness, from the gate.**  Osin's torsion clause over a free
product of torsion-free factors, with the classification and the factor
embedding both supplied by the relative Greendlinger transfer. -/
theorem torsionFree (hgate : RelativeGreendlingerGate S B)
    (hS : IsPowerTorsionFree S) (hB : IsPowerTorsionFree B) :
    IsPowerTorsionFree D.Routed := by
  obtain ⟨hlen, htor⟩ :=
    hgate D.relators D.relators_cyclicallyReduced D.relators_long D.metric
  exact isPowerTorsionFree_of_torsionIntoFactors htor
    (factorMap_injective_of_cyclicallyReduced hlen D.relators_cyclicallyReduced)
    (factor_isPowerTorsionFree hS hB)

/-- **Protected survival, from the gate.**  The source factor embeds, so the
only way to kill `s` is to kill it in the first stage, which
`protected_survives` forbids. -/
theorem protected_injOn (hgate : RelativeGreendlingerGate S B) :
    Set.InjOn D.route ({1, s} : Set E) := by
  obtain ⟨hlen, -⟩ :=
    hgate D.relators D.relators_cyclicallyReduced D.relators_long D.metric
  have hinj : Function.Injective (routeOf D.relators) :=
    factorMap_injective_of_cyclicallyReduced hlen D.relators_cyclicallyReduced
      false
  refine injOn_pair fun h1 => ?_
  by_contra hs
  refine D.protected_survives hs (hinj ?_)
  rw [map_one]
  exact h1

/-- **The router's output.**  Every field of the frozen interface, derived from
the design and the gate. -/
noncomputable def routerData [N.Normal] [Group.IsFinitelyPresented S]
    [Group.IsFinitelyPresented B] (hgate : RelativeGreendlingerGate S B)
    (hS : IsPowerTorsionFree S) (hB : IsPowerTorsionFree B) :
    SmallCancellationRouter.RoutingLemmaData E N s B where
  Quotient := D.Routed
  groupQuotient := inferInstance
  route := D.route
  route_surjective := D.route_surjective
  partner := D.partner
  partner_surjective := D.partner_surjective
  finitelyPresented := D.finitelyPresented
  defect_top := D.defect_top
  protected_injOn := D.protected_injOn hgate
  generatorOne := D.genOne
  generatorTwo := D.genTwo
  generates := D.generates
  torsionFree := D.torsionFree hgate hS hB

/-! ## 5.  What the design cannot do, proved

The small-cancellation stage keeps every factor of a free product embedded —
that is `factorMap_injective_of_cyclicallyReduced`, and it is the whole content
of Osin's peripheral clause in the free-product case.  Against `defect_top`,
which forces the source factor to *surject*, that is decisive. -/

/-- **The source factor is never collapsed.**  Under the Greendlinger length
bound the routing map out of the source factor is a bijection. -/
theorem routeOf_bijective (hlen : GreendlingerLengthBound D.relators) :
    Function.Bijective (routeOf D.relators) :=
  ⟨factorMap_injective_of_cyclicallyReduced hlen D.relators_cyclicallyReduced
      false,
    D.routeOf_surjective⟩

/-- The source factor *is* the routed quotient. -/
noncomputable def sourceEquivRouted (hlen : GreendlingerLengthBound D.relators) :
    S ≃* D.Routed :=
  MulEquiv.ofBijective (routeOf D.relators) (D.routeOf_bijective hlen)

/-- **All of the saturation happens before the free product.**  Under the
length bound — which is exactly what the gate delivers — the designated normal
subgroup already fills the source factor, so the free-product
small-cancellation stage contributes nothing to `defect_top`.  In particular a
design with `S = E` and `pre = id` forces `N = ⊤`: the single-stage reading of
the router construction is satisfiable only when the source is already the
answer. -/
theorem defect_eq_top_of_lengthBound
    (hlen : GreendlingerLengthBound D.relators) : N.map D.pre = ⊤ := by
  obtain ⟨hinj, hsurj⟩ := D.routeOf_bijective hlen
  have h1 : (N.map D.pre).map (routeOf D.relators) = ⊤ := by
    rw [Subgroup.map_map]
    exact D.defect_top
  have h2 : (⊤ : Subgroup S).map (routeOf D.relators) = ⊤ :=
    Subgroup.map_top_of_surjective _ hsurj
  exact Subgroup.map_injective hinj (h1.trans h2.symm)

end RouterRelatorDesign

end BespokeRouter
end GroupApproximation
