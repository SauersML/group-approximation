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

## What is proved here from DGO's Theorem 5.3

`injOn_cayleyBall_of_rotatingQuotient`: the injectivity-on-a-ball clause of
Theorem 5.1 follows from the injectivity radius of `RotatingQuotient`, because
the cone-off does not increase word length and the displacement of the
basepoint of a Cayley graph is the word length
(`HullSC.injOn_cayleyBall_of_dist_lt`).  Choosing the separation `ρ` above
`2R` -- that is, taking the relator deep enough -- prescribes the radius.

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

/-- **Hull, Corollary 5.7 with Lemma 5.8** (after DGO, Theorem 6.14): a
suitable subgroup contains a subgroup that is hyperbolically embedded in the
ambient group with respect to Hull's alphabet.

This is what makes Theorem 5.1 applicable inside `N`.  It is close to, but not
the same as, `GGT.DGOTheorem68`: that theorem produces `E(g) ↪_h (G, X)` for
*some* relative generating set `X`, while the statement below asks for the
hyperbolic embedding over Hull's `A`, which is what the injectivity radius of
the quotient is measured against.  Bridging the two is Hull's Theorem 3.12,
step (2) of the plan in `GGT/HullSC.lean`. -/
def ExistsHypEmbeddedInSuitable : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N →
      ∃ H : Subgroup G, H ≤ N ∧ GGT.IsHypEmbeddedOf G A.alphabet.carrier H

/-- **Hull, Theorem 5.1 with the relator of his §6.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let
> `H ≤ N ≤ G` with `H ↪_h (G, A)` and `N` suitable, let `S₁, …, S_k ≤ G` be
> suitable, let `t ∈ G` and let `R` be a radius.  Then there is `u ∈ N` such
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
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (H N : Subgroup G),
    GGT.IsHypEmbeddedOf G A.alphabet.carrier H → H ≤ N →
      Suitable A.alphabet N → ∀ {k : ℕ} (S : Fin k → Subgroup G),
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
every `m`, and with `HullSCCommonQuotient.hullCommonQuotient_of_tower` it
closes Hull's Corollary 7.4. -/
theorem hullOneStep_of_theorem51 (hEmb : ExistsHypEmbeddedInSuitable.{u})
    (h51 : HullTheorem51Statement.{u}) : HullOneStepStatement.{u} := by
  intro G _ A N hN k S hS t R
  obtain ⟨H, hHN, hHemb⟩ := hEmb A hN
  obtain ⟨u, huN, ⟨D⟩⟩ := h51 A H N hHemb hHN hN S hS t R
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

/-! ## What DGO's Theorem 5.3 supplies -/

/-- **The injectivity clause of Theorem 5.1, from DGO's Theorem 5.3.**

The rotating family of Hull's proof lives on the cone-off of `Γ(G,A)` along the
cosets of the hyperbolically embedded `H`, so DGO's injectivity radius is a
statement about displacement in the cone-off.  Coning off does not increase
word length and the displacement of the basepoint of a Cayley graph *is* the
word length, so an injectivity radius above `2R` in the cone-off is injectivity
on the `R`-ball of `Γ(G,A)`.  Taking the separation `ρ` above `2R` -- which is
what "take the relator deep enough" does -- prescribes the radius.

This is the one clause of Theorem 5.1 that DGO's Theorem 5.3 gives outright.
The alphabet clauses do not follow from it; see the module header. -/
theorem injOn_cayleyBall_of_rotatingQuotient {G : Type u} [Group G]
    (A : HullGeneratingSet G) (H : Subgroup G) {ρ : ℝ} (R : ℕ)
    (hρ : 2 * (R : ℝ) < ρ)
    {C : Set (Cayley (coneOff A.alphabet H).alphabet)}
    {Rot : Cayley (coneOff A.alphabet H).alphabet → Subgroup G}
    (D : RotatingQuotient ρ C Rot) :
    Set.InjOn D.q (cayleyBall A.alphabet R) := by
  refine injOn_cayleyBall_of_dist_lt (L := D.injRadius) A.alphabet H D.q R ?_ ?_
  · have hsep := D.separation_le_injRadius
    linarith
  · intro g hg hdist
    exact D.ne_one_of_dist_lt g hg _ hdist

end HullSC
end GroupApproximation
