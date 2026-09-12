import GroupApproximation.GGT.HullSC

/-!
# Hull's Theorem 5.1, and Theorem 7.1 for one relator from it

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §5 and §6.

`GGT/HullSC.lean` reduces both manuscript targets to `HullOneStepStatement` --
Hull's Theorem 7.1 for a single target element.  This module splits that
citation along the seam of Hull's own proof:

* **§5 gives the quotient.**  `HullTheorem51Statement`: for a hyperbolically
  embedded `H ≤ N` there is an element `u ∈ N` such that killing the single
  relator `t⁻¹u` leaves a quotient that is acylindrically hyperbolic over the
  image alphabet, injective on the prescribed ball, keeps the prescribed
  suitable subgroups suitable, and lifts finite order.
* **§6 chooses the relator.**  `u = h₁^{n₁}h₂^{n₂}⋯` in the two independent
  loxodromics of `N`, with the exponents large enough that `t⁻¹u` satisfies
  Hull's condition `C(ε, μ, ρ)` over `H`.  The existential `∃ u ∈ N` in the
  statement above *is* that choice.
* **The two clauses that mention `t` are then theorems, not citations.**
  `hullOneStep_of_theorem51` proves them: `q(t⁻¹u) = 1` gives `q(t) = q(u)`,
  and `u ∈ N` gives `q(t) ∈ q(N)`; and `ker q` is the normal closure of the
  single element `t⁻¹u`, which is the manuscript's separate remark on Hull's
  construction at `m = 1`.

So `HullOneStepStatement` stops being a leaf.  What replaces it as leaves is
strictly less: the quotient theorem of §5, and the fact that a suitable
subgroup contains a hyperbolically embedded one.

## What the relator is, and why it is not an element of `H`

Hull's relator is `W = t⁻¹u`, a *word* in the alphabet `X ⊔ H`: one syllable
spelling `t⁻¹` in `X`, then alternating `H`-letters `h₁^{nᵢ}` and `X`-syllables
spelling `h₂^{nⱼ}`.  It is not an element of `H`, and that is exactly why
Theorem 7.1 does not follow from group-theoretic Dehn filling (DGO Thm 7.19),
whose relators lie inside the hyperbolically embedded subgroups: filling kills
elements of `H`, it does not identify `t` with an element of `N`.  The
statement below therefore quantifies over `u ∈ N` and takes the relator to be
`t⁻¹u ∈ G`, which is where Hull's small cancellation condition, not filling,
is the input.

## Where the injectivity clause went, and the lifting clause with it

This module used to derive the injectivity-on-a-ball clause of Theorem 5.1 from
an injectivity radius carried by `RotatingQuotient`.  It no longer does, and the
route is `HullSCFilling.injOn_cayleyBall_of_kernel_moves` from
`HullSCFilling.RotatingData.kernel_moves_base`: reading DGO's Theorem 5.3
against the source shows it concludes the free splitting and the dichotomy and
nothing metric, so the injectivity radius is Hull's §5 and belongs with the
family Hull builds.  `GGT/HullSCDGO.lean` carries the audit.

The lifting of finite order made the same journey afterwards and for a harder
reason (issue #50): it was not merely misattributed but false in the position it
occupied, which `GGT/DGORotatingQuotientRefutation.lean` proves.  It is
`HullSCFilling.RotatingData.finiteOrder_lift`, and `HullFillingQuotient` still
carries it as a clause of Theorem 5.1 -- only its source has moved.

What DGO's Theorem 5.3 does **not** give, and what stays inside
`HullTheorem51Statement`, is everything about the *alphabet*: that the quotient
carries a Hull generating set containing the image of `A`, and that the images
of the prescribed suitable subgroups are suitable in it.  Those come from the
other half of Hull's §5 -- the images of hyperbolically embedded subgroups are
hyperbolically embedded in the quotient -- which is a statement about relative
generating sets, so it cannot be a field of `RotatingQuotient`: that structure
is indexed by an abstract metric space with a group action and has no alphabet
to speak of.  Adding one would be adding a different theorem under the name of
DGO's.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## The output of Hull's Theorem 5.1 -/

/-- **The quotient of Hull's Theorem 5.1**, by the normal closure of a single
relator `w`.  Its fields are `HullStep`'s, together with the identification of
the kernel that makes the relator visible. -/
structure HullFillingQuotient {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) {k : ℕ} (S : Fin k → Subgroup G) (w : G) (R : ℕ) where
  /-- The quotient group. -/
  Q : Type u
  /-- Its group structure. -/
  [group : Group Q]
  /-- The quotient map. -/
  q : G →* Q
  /-- The quotient map is onto. -/
  surjective : Function.Surjective q
  /-- Its kernel is the normal closure of the relator. -/
  ker_eq : q.ker = Subgroup.normalClosure ({w} : Set G)
  /-- Hull's alphabet for the quotient. -/
  hullSet : HullGeneratingSet Q
  /-- It contains the image of Hull's alphabet for `G`. -/
  alphabet_image : ∀ a ∈ A.alphabet.carrier, q a ∈ hullSet.alphabet.carrier
  /-- The quotient map is injective on the `R`-ball of `Γ(G,A)`. -/
  injOn : Set.InjOn q (cayleyBall A.alphabet R)
  /-- The image of `N` is suitable in the quotient. -/
  suitable_map : Suitable hullSet.alphabet (N.map q)
  /-- The image of each prescribed suitable subgroup is suitable. -/
  suitable_map_family : ∀ j : Fin k, Suitable hullSet.alphabet ((S j).map q)
  /-- Finite order lifts, with the order preserved. -/
  finiteOrder_lift :
    ∀ y : Q, IsOfFinOrder y → ∃ g : G, q g = y ∧ orderOf g = orderOf y

namespace HullFillingQuotient

instance instGroup {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G} {w : G} {R : ℕ}
    (D : HullFillingQuotient A N S w R) : Group D.Q := D.group

/-- Forgetting the relator gives a step of Hull's tower. -/
def toHullStep {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G} {w : G} {R : ℕ}
    (D : HullFillingQuotient A N S w R) : HullStep A N S R where
  Q := D.Q
  group := D.group
  q := D.q
  surjective := D.surjective
  hullSet := D.hullSet
  alphabet_image := D.alphabet_image
  injOn := D.injOn
  suitable_map := D.suitable_map
  suitable_map_family := D.suitable_map_family
  finiteOrder_lift := D.finiteOrder_lift

end HullFillingQuotient

/-! ## The two citations that replace `HullOneStepStatement` -/

/-- **The hyperbolically embedded subgroup Hull's Theorem 5.1 runs over.**

`H ↪_h (G, A)` over Hull's own alphabet, together with the loxodromic element
of `H` whose long powers are the relator's `H`-letters.

**Why the loxodromic field is not decoration.**  A subgroup *contained* in the
alphabet is elliptic (`HullSC.not_isLoxodromic_of_subgroup_subset`, the
`Alphabet` form of `GGT.RelGenSet.not_isLoxodromic_of_mem_fam`) and is not
hyperbolically embedded over it either
(`GGT.not_isHypEmbeddedOf_of_subset`).  Without `lox` this structure would be
satisfied by `H = ⊥` and would give Theorem 5.1 nothing.  With it, `not_subset`
below proves `H ⊄ A`, so the refutation does not apply and the citation is
neither false nor vacuous.

An earlier draft of this lane asked instead that Hull's alphabet *be* the
cone-off of a base along `H`.  That was an over-correction: it forces
`H ⊆ A`, hence `H` elliptic, hence `H` useless as a source of relator letters.
The subgroup `H₀` that Osin's Theorem 5.4 cones off to build `A`, and the
subgroup `H = E(g)` the small cancellation runs over, are different subgroups
-- the second contains a loxodromic of `Γ(G,A)` and so cannot be inside `A`.

Two independent guards now rule that mistake out.  `not_subset` below derives
`H ⊄ A` from the loxodromic field; and
`GGT.RelGenSet.not_isHyperbolicallyEmbedded_of_base_supset_alphabet` -- a
subgroup cannot be coned off twice -- refutes `embedded` outright for anyone who
composes Osin's Theorem 5.4 with DGO's Theorem 6.8 and reuses the same
family. -/
structure HypEmbeddedCore {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) where
  /-- The relative generating set, with Hull's alphabet as its base. -/
  rel : GGT.RelGenSet G Unit
  /-- Its base is Hull's alphabet. -/
  base_eq : rel.base = A.alphabet.carrier
  /-- The hyperbolically embedded subgroup. -/
  H : Subgroup G
  /-- It is the family of `rel`. -/
  fam_eq : rel.fam = fun _ => H
  /-- It lies inside the suitable subgroup, so the relator's `H`-letters do. -/
  le : H ≤ N
  /-- `H ↪_h (G, A)`. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The element whose long powers are the relator's `H`-letters. -/
  lox : G
  /-- It lies in `H`. -/
  lox_mem : lox ∈ H
  /-- It is loxodromic on `Γ(G,A)`. -/
  lox_isLoxodromic : IsLoxodromic lox (Cayley.base A.alphabet)

namespace HypEmbeddedCore

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- The core witnesses `H ↪_h (G, A)` in `GGT`'s vocabulary. -/
theorem isHypEmbeddedOf (E : HypEmbeddedCore A N) :
    GGT.IsHypEmbeddedOf G A.alphabet.carrier E.H :=
  ⟨E.rel, E.base_eq, E.fam_eq, E.embedded⟩

/-- **The core is not vacuous and not refuted**: its subgroup is not contained
in Hull's alphabet, because it contains a loxodromic element. -/
theorem not_subset (E : HypEmbeddedCore A N) :
    ¬ (E.H : Set G) ⊆ A.alphabet.carrier :=
  not_subset_of_isLoxodromic A.alphabet E.lox_mem E.lox_isLoxodromic

/-- **Hull's alphabet is a subset of the coned-off alphabet.**  It is the base
of `rel`, and a base is contained in the alphabet it generates. -/
theorem base_subset_alphabet (E : HypEmbeddedCore A N) :
    A.alphabet.carrier ⊆ E.rel.alphabet.carrier := by
  rw [← E.base_eq]
  show E.rel.base ⊆ E.rel.base ∪ ⋃ lam : Unit, (E.rel.fam lam : Set G)
  exact Set.subset_union_left

/-- **Balls of `Γ(G,A)` sit inside balls of the cone-off, at the same radius.**

This is the direction Hull's Theorem 5.1 is consumed along: the small
cancellation geometry lives on `Γ(G, A ⊔ H)`, so its injectivity radius is a
statement there, and it restricts to `Γ(G,A)` because coning off only shortens
words.  It is also the check that `base_eq` is the right field: had the core
identified `A` with the *coned-off* alphabet instead of with the base, this
inclusion would be an equality carrying no information, and the subgroup would
be elliptic and useless. -/
theorem cayleyBall_subset (E : HypEmbeddedCore A N) (R : ℕ) :
    cayleyBall A.alphabet R ⊆ cayleyBall E.rel.alphabet R := by
  intro x hx
  rw [mem_cayleyBall_iff] at hx ⊢
  refine le_trans ?_ hx
  unfold wordDist
  exact wordNorm_mono E.base_subset_alphabet
    (wordLengths_nonempty A.alphabet.symmetricGenerating _)

/-- In particular the subgroup is nontrivial: a loxodromic element has infinite
order. -/
theorem ne_bot (E : HypEmbeddedCore A N) : E.H ≠ ⊥ := by
  intro hbot
  have h1 : E.lox = 1 := by
    have hmem := E.lox_mem
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hfin : IsOfFinOrder E.lox := by
    rw [h1]
    exact IsOfFinOrder.one
  exact not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic hfin

end HypEmbeddedCore

/-- **Hull, Corollary 5.7 with Lemma 5.8** (after DGO, Theorem 6.14, and Osin,
Theorem 5.4): a suitable subgroup contains a subgroup that is hyperbolically
embedded in the ambient group, over a relative generating set whose cone-off is
Hull's alphabet.

This is what makes Theorem 5.1 applicable inside `N`.  It is strictly stronger
than `GGT.DGOTheorem68`, which produces `E(g) ↪_h (G, X)` for *some* `X` with
no relation to a prescribed alphabet; the enlargement that makes the coned-off
action acylindrical is `GGT.OsinTheorem54`, and it is in general infinite, so
`GGT.DGOCorollary427` -- hyperbolic embeddedness is invariant under finite
symmetric difference of the base -- does not bridge the gap.  Recorded as a
separate citation for that reason rather than derived from `GGT.DGOTheorem68`. -/
def ExistsHypEmbeddedInSuitable : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N → Nonempty (HypEmbeddedCore A N)

/-- **Hull, Theorem 5.1 with the relator of his §6.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable and let `H ≤ N` be hyperbolically embedded over a base whose
> cone-off is `A`, let `S₁, …, S_k ≤ G` be suitable, let `t ∈ G` and let `R` be
> a radius.  Then there is `u ∈ N` such
> that the quotient of `G` by the normal closure of the single relator `t⁻¹u`
> is acylindrically hyperbolic over an alphabet containing the image of `A`, is
> injective on the `R`-ball of `Γ(G,A)`, carries `N` and every `Sⱼ` to suitable
> subgroups, and lifts elements of finite order to elements of the same order.

The existential is Hull's §6: `u = h₁^{n₁}h₂^{n₂}⋯` in two independent
loxodromics of `N`, with exponents large enough that `t⁻¹u` satisfies his
condition `C(ε, μ, ρ)` over `H`.  Over a torsion-free ambient group the two
loxodromics are supplied by
`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`, which
is proved; what is cited is that the exponents can be chosen, and that the
resulting quotient has the listed properties. -/
def HullTheorem51Statement : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G),
    HypEmbeddedCore A N → Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ (t : G) (R : ℕ),
          ∃ u ∈ N, Nonempty (HullFillingQuotient A N S (t⁻¹ * u) R)

/-! ## Theorem 7.1 for one relator, from Theorem 5.1 -/

/-- **Hull's Theorem 7.1 at `m = 1`, from his Theorem 5.1.**

The two clauses of Theorem 7.1 that mention the target `t` are proved here
rather than cited:

* `q(t) ∈ q(N)` -- the relator `t⁻¹u` dies in the quotient, so `q(t) = q(u)`,
  and `u` was chosen in `N`;
* `ker q` is normally generated by one element -- it is the normal closure of
  `t⁻¹u`, which is the manuscript's separate remark on Hull's construction, at
  `m = 1`.

Everything else is passed through from Theorem 5.1 unchanged.  With
`HullSC.hullTower_of_oneStep` above this closes the manuscript's `thm:hull` for
every `m`, and with `HullSC.hullCommonQuotient_of_tower_corrected` it closes
Hull's Corollary 7.4. -/
theorem hullOneStep_of_theorem51 (hEmb : ExistsHypEmbeddedInSuitable.{u})
    (h51 : HullTheorem51Statement.{u}) : HullOneStepStatement.{u} := by
  intro G _ _hG A N hN k S hS t R
  obtain ⟨E⟩ := hEmb A hN
  obtain ⟨u, huN, ⟨D⟩⟩ := h51 A N E hN S hS t R
  have hrel : D.q (t⁻¹ * u) = 1 := by
    rw [← MonoidHom.mem_ker, D.ker_eq]
    exact Subgroup.subset_normalClosure rfl
  have hqt : D.q t = D.q u := by
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel
  refine ⟨{ step := D.toHullStep
            mem_map := ?_
            kerNormallyGenerated := ⟨{t⁻¹ * u}, by simp, ?_⟩ }⟩
  · intro _
    show D.q t ∈ N.map D.q
    rw [hqt]
    exact Subgroup.mem_map_of_mem _ huN
  · show D.q.ker = Subgroup.normalClosure ((({t⁻¹ * u} : Finset G)) : Set G)
    rw [D.ker_eq, Finset.coe_singleton]

end HullSC
end GroupApproximation
