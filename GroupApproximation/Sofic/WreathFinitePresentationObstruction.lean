import GroupApproximation.Algebra.GraphProduct
import GroupApproximation.Sofic.AscendingHNNDoubleCosets

/-!
# Finitely many pair-orbits cannot cover an infinite-orbit square

`Algebra/GraphProduct` supplies the algebraic half of Lemma 54.3: in a graph
product, two vertex groups at *distinct* sites commute only if the sites are
adjacent (`adj_of_commute_vertex`).  `Sofic/AscendingHNNDoubleCosets` supplies
Lemma 54.4: the diagonal action on the square of the HNN coset space has
infinitely many orbits, because the height homomorphism separates
`(Γ, tⁿΓ)` for distinct `n`.

Missing between them is the counting step, and it is what this file adds.  A
finite presentation of the wreath product yields only *finitely many* normal
generators, so only finitely many `G`-orbits of site-pairs can appear among the
cross-site commutators; the graph product over that edge set then has to equal
the wreath product, in which all distinct-site lamps commute, forcing the graph
to be complete.  Against infinitely many orbits that is impossible.

The counting step is proved here in general -- no lamps, no HNN, no coronas:

* `exists_not_adj_of_finitely_many_orbits` -- an adjacency covered by finitely
  many orbits of pairs must omit some pair, as soon as the square carries
  infinitely many orbits of pairs with distinct components;
* `exists_not_commute_vertex_of_finitely_many_orbits` -- consequently the graph
  product over such an adjacency has two distinct-site vertex groups that do
  **not** commute, so it is not the restricted direct product and hence not the
  lamp subgroup of a permutational wreath product.

What is *not* claimed: the Tietze bookkeeping that produces the finite edge set
from a finite presentation.  `Algebra/TietzeFinitePresentation` has the
ingredients (`ker_eq_normalClosure`, `normalClosure_image_finite`); assembling
them into "finitely presented implies finitely many pair-orbits" is the
remaining step, and this file states the counting half it would feed.
-/

namespace GroupApproximation

universe u v w

/-! ## The counting step, in general -/

/-- **Finitely many orbits cannot cover everything.**

If every adjacent pair lies in one of finitely many `G`-orbits, while some
infinite family of pairs with distinct components occupies pairwise distinct
orbits, then some pair of distinct points is non-adjacent.

The proof is a pigeonhole: were every distinct pair adjacent, each member of the
infinite family would fall in one of the finitely many listed orbits, and the
orbit map would be an injection of an infinite type into a finite one. -/
theorem exists_not_adj_of_finitely_many_orbits
    {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (adj : X → X → Prop) (F : Finset (X × X))
    (hcover : ∀ x y : X, adj x y → ∃ p ∈ F, (x, y) ∈ MulAction.orbit G p)
    {ι : Type w} [Infinite ι] (w : ι → X × X)
    (hw : Function.Injective fun i => MulAction.orbit G (w i))
    (hne : ∀ i, (w i).1 ≠ (w i).2) :
    ∃ x y : X, x ≠ y ∧ ¬ adj x y := by
  classical
  by_contra hcon
  push Not at hcon
  -- every distinct pair is adjacent, so each `w i` is covered by a listed orbit
  choose p hpF hp using fun i : ι =>
    hcover (w i).1 (w i).2 (hcon (w i).1 (w i).2 (hne i))
  have hinj : Function.Injective p := by
    intro i j hij
    refine hw ?_
    show MulAction.orbit G (w i) = MulAction.orbit G (w j)
    have h1 : MulAction.orbit G (w i) = MulAction.orbit G (p i) :=
      MulAction.orbit_eq_iff.mpr (hp i)
    have h2 : MulAction.orbit G (w j) = MulAction.orbit G (p j) :=
      MulAction.orbit_eq_iff.mpr (hp j)
    rw [h1, h2, hij]
  -- an injection of an infinite type into a finite set
  haveI : Fintype {q : X × X // q ∈ F} := FinsetCoe.fintype F
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun i : ι => (⟨p i, hpF i⟩ : {q : X × X // q ∈ F}))
  exact hij (hinj (congrArg Subtype.val heq))

/-! ## The graph-product consequence -/

open GraphProduct in
/-- **The contradiction of Lemma 54.3, assembled.**

Over an adjacency covered by finitely many orbits, the graph product has two
distinct sites whose vertex groups fail to commute.  In the lamp subgroup of a
permutational wreath product distinct-site lamps *do* commute, so the two groups
are different: a finite edge set can never present the wreath product. -/
theorem exists_not_commute_vertex_of_finitely_many_orbits
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [DecidableEq X]
    {K : Type u} [Group K] [Nontrivial K]
    (adj : X → X → Prop) (hG : IsSimplicial adj) (F : Finset (X × X))
    (hcover : ∀ x y : X, adj x y → ∃ p ∈ F, (x, y) ∈ MulAction.orbit G p)
    {ι : Type w} [Infinite ι] (w : ι → X × X)
    (hw : Function.Injective fun i => MulAction.orbit G (w i))
    (hne : ∀ i, (w i).1 ≠ (w i).2) :
    ∃ x y : X, x ≠ y ∧
      ∃ k l : K, ¬ Commute (vertex (K := K) adj x k) (vertex (K := K) adj y l) := by
  obtain ⟨x, y, hxy, hnadj⟩ :=
    exists_not_adj_of_finitely_many_orbits adj F hcover w hw hne
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  exact ⟨x, y, hxy, k, k, not_commute_vertex_of_not_adj hG hxy hnadj hk hk⟩

/-! ## The ascending-HNN coset space -/

namespace MarkedCompression

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- The root coset is moved by every nonzero power of the stable letter: a
fixing element would have height one, and `tᵏ` has height `k`. -/
theorem rootCoset_ne_zpow_smul {k : ℤ} (hk : k ≠ 0) :
    rootCoset α hα ≠ (tVertical α hα ^ k) • rootCoset α hα := by
  intro h
  refine no_diagonal_transport α hα (m := 0) (n := k) (Ne.symm hk) 1
    (one_smul _ _) ?_
  simpa using h

include hα in
/-- **Lemma 54.3 meets Lemma 54.4.**  On the ascending-HNN coset space no
adjacency covered by finitely many orbits of site-pairs can be complete: the
pairs `(Γ, tⁿ⁺¹Γ)` occupy infinitely many distinct orbits, and each has distinct
components.

So a finite edge set -- all a finite presentation could ever supply -- always
leaves two distinct sites non-adjacent. -/
theorem exists_not_adj_cosets_of_finitely_many_orbits
    (adj : Cosets α hα → Cosets α hα → Prop)
    (F : Finset (Cosets α hα × Cosets α hα))
    (hcover : ∀ x y : Cosets α hα, adj x y →
      ∃ p ∈ F, (x, y) ∈ MulAction.orbit (Vertical α hα) p) :
    ∃ x y : Cosets α hα, x ≠ y ∧ ¬ adj x y := by
  refine exists_not_adj_of_finitely_many_orbits adj F hcover (ι := ℕ)
    (fun n => (rootCoset α hα,
      (tVertical α hα ^ ((n : ℤ) + 1)) • rootCoset α hα)) ?_ ?_
  · have hcast : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
      intro a b hab
      simp only [add_left_inj, Nat.cast_inj] at hab
      exact hab
    exact (injective_diagonal_orbit α hα).comp hcast
  · intro n
    have hpos : (0 : ℤ) < (n : ℤ) + 1 := by positivity
    exact rootCoset_ne_zpow_smul α hα hpos.ne'

end MarkedCompression

end GroupApproximation
