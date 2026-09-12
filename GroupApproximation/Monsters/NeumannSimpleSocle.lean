import GroupApproximation.Monsters.NeumannTwoGenerator
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Neumann's invariant: recovering the index set from the group

`Monsters/NeumannTwoGenerator` reduced `UN.07` to the construction of a
two-generated family indexed by subsets of `ℕ` together with an
isomorphism-invariant recovering the subset, and proved the *elementary* half
of Neumann's invariant (a subdirect product has every factor as a quotient).
This file proves the other half, which is where the argument actually lives.

## Why the quotient formulation had to be abandoned

Neumann's group is `G_S = ⟨a, b⟩ ≤ ∏_{n ∈ S} Alt(n)`, and the invariant is
supposed to be "the alternating groups occurring in `G_S`".  The tempting
reading -- *`Alt(m)` is a quotient of `G_S` iff `m ∈ S`* -- cannot be proved
from the subdirect structure, and the reason is not a gap in the argument: an
infinite product of finite groups has simple quotients that are none of its
factors, namely its ultraproducts.  So a converse phrased through quotients is
a statement about the finitely generated subgroup and not about the product.

The formulation that *is* a statement about the product is through **simple
normal subgroups**, and it is unconditional:

> if `G ≤ ∏_i Q_i` is subdirect and every `Q_i` is simple, then every simple
> group isomorphic to a normal subgroup of `G` is isomorphic to some `Q_i`.

That is `exists_mulEquiv_factor`.  Nothing about finite generation,
alternating groups, permutations or cardinality enters; it is four lines of
simplicity chasing, done below in full.

## Contents

* `coordHom`, `IsSubdirect` --- the coordinate maps of a subgroup of a
  product, and subdirectness.
* `mulEquiv_of_surjective_of_isSimpleGroup` --- a surjection from a simple
  group onto a nontrivial group is an isomorphism.  (Mathlib has
  `IsSimpleGroup.isSimpleGroup_of_surjective`, which transports simplicity but
  does not say the map is injective.)
* `exists_mulEquiv_factor` --- **the remaining half**, as displayed above.
* `normalFactorSet` --- the invariant `{i | Q i occurs as a normal subgroup}`,
  and `normalFactorSet_congr`, that it is an isomorphism invariant.
* `piFactor` and `exists_normal_mulEquiv_of_factor_mem` --- the reverse
  inclusion, for a subgroup containing each factor.
* `normalFactorSet_eq_of_subsetProduct` --- **the recovery theorem**: for
  `G ≤ ∏_{n ∈ S} Q n` subdirect and containing every factor, with the `Q n`
  simple and pairwise nonisomorphic, `normalFactorSet Q G = S` exactly.

## What `UN.07` now needs, and only that

`normalFactorSet_eq_of_subsetProduct` consumes three things about Neumann's
`G_S`: subdirectness, that it contains each factor, and that the factors are
simple and pairwise nonisomorphic.  The last is `alternatingGroup.isSimpleGroup`
(`5 ≤ Nat.card α`, in Mathlib) together with the orders `n!/2` being distinct.
The first two are the *same* single input: the generation lemma
`⟨(1 2 3), (1 2 … n)⟩ = Alt(n)` for odd `n ≥ 5`, from which both the surjectivity
of every coordinate and the presence of every factor follow by the standard
commutator argument.  Mathlib has `alternatingGroup`, three-cycle generation and
simplicity, but nothing about that pair, and the standard proof (conjugate the
three-cycle by powers of the `n`-cycle to reach every `(i, i+1, i+2)`) is a
genuine induction.  That lemma is now the *only* thing between this development
and Neumann's literal two-generator family.

## Manuscript status

Infrastructure for `UN.07`; certifies no manuscript step by itself.  The
printed clause *"for instance Neumann's two-generator groups"* remains an
illustration; the sentence the paragraph uses is certified by
`NeumannContinuum.manuscriptContinuumMultiplicityUnconditional`.
-/

namespace GroupApproximation
namespace NeumannSimpleSocle

universe u v

/-! ## Coordinates of a subgroup of a product -/

section Coord

variable {ι : Type u} {Q : ι → Type v} [∀ i, Group (Q i)]

/-- The `i`-th coordinate map, restricted to a subgroup of the product. -/
def coordHom (G : Subgroup (∀ i, Q i)) (i : ι) : G →* Q i :=
  (Pi.evalMonoidHom Q i).comp G.subtype

@[simp] theorem coordHom_apply (G : Subgroup (∀ i, Q i)) (i : ι) (g : G) :
    coordHom G i g = (g : ∀ i, Q i) i := rfl

/-- A subgroup of a product is **subdirect** when every coordinate map is
onto. -/
def IsSubdirect (G : Subgroup (∀ i, Q i)) : Prop :=
  ∀ i, Function.Surjective (coordHom G i)

end Coord

/-! ## A surjection out of a simple group is an isomorphism -/

/-- **A surjective homomorphism from a simple group onto a nontrivial group is
an isomorphism.**  Its kernel is normal, hence `⊥` or `⊤`; `⊤` would make the
map trivial and so not onto a nontrivial group. -/
theorem mulEquiv_of_surjective_of_isSimpleGroup {H K : Type*} [Group H] [Group K]
    [IsSimpleGroup H] [Nontrivial K] (f : H →* K) (hf : Function.Surjective f) :
    Nonempty (H ≃* K) := by
  rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with hbot | htop
  · exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hbot, hf⟩⟩
  · exfalso
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    obtain ⟨h, hh⟩ := hf k
    have hmem : h ∈ f.ker := by rw [htop]; exact Subgroup.mem_top h
    rw [MonoidHom.mem_ker] at hmem
    exact hk (by rw [← hh]; exact hmem)

/-! ## The remaining half of Neumann's invariant -/

section Factor

variable {ι : Type u} {Q : ι → Type v} [∀ i, Group (Q i)] [∀ i, IsSimpleGroup (Q i)]

/-- **The remaining half.**  In a subdirect subgroup of a product of simple
groups, every simple group isomorphic to a normal subgroup is isomorphic to one
of the factors.

Applied to Neumann's `G_S ≤ ∏_{n ∈ S} Alt(n)` with pairwise nonisomorphic
factors, this is exactly *"`Alt(m)` occurs in `G_S` only for `m ∈ S`"*. -/
theorem exists_mulEquiv_factor {K : Type*} [Group K] [IsSimpleGroup K]
    {G : Subgroup (∀ i, Q i)} (hG : IsSubdirect G)
    {N : Subgroup G} (hN : N.Normal) (e : N ≃* K) :
    ∃ i, Nonempty (K ≃* Q i) := by
  by_cases hall : ∀ i, N.map (coordHom G i) = ⊥
  · exfalso
    have hone : ∀ n : N, n = 1 := by
      intro n
      have hcoord : ∀ i, ((n : G) : ∀ j, Q j) i = 1 := by
        intro i
        have hmem : coordHom G i (n : G) ∈ N.map (coordHom G i) :=
          Subgroup.mem_map_of_mem _ n.2
        rw [hall i, Subgroup.mem_bot] at hmem
        exact hmem
      have hval : ((n : G) : ∀ j, Q j) = 1 := funext hcoord
      exact Subtype.ext (Subtype.ext hval)
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    apply hk
    calc k = e (e.symm k) := (e.apply_symm_apply k).symm
      _ = e 1 := by rw [hone (e.symm k)]
      _ = 1 := map_one e
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hnm : (N.map (coordHom G i)).Normal := hN.map (coordHom G i) (hG i)
    have htop : N.map (coordHom G i) = ⊤ := hnm.eq_bot_or_eq_top.resolve_left hi
    have hsurj : Function.Surjective
        (((coordHom G i).comp N.subtype).comp e.symm.toMonoidHom) := by
      intro q
      have hq : q ∈ N.map (coordHom G i) := by
        rw [htop]; exact Subgroup.mem_top q
      rw [Subgroup.mem_map] at hq
      obtain ⟨x, hx, hxq⟩ := hq
      refine ⟨e ⟨x, hx⟩, ?_⟩
      show coordHom G i (N.subtype (e.symm (e ⟨x, hx⟩))) = q
      rw [e.symm_apply_apply]
      exact hxq
    exact ⟨i, mulEquiv_of_surjective_of_isSimpleGroup _ hsurj⟩

end Factor

/-! ## The invariant -/

section Invariant

variable {ι : Type u} (Q : ι → Type v) [∀ i, Group (Q i)]

/-- **The invariant.**  The set of indices whose factor occurs as a normal
subgroup.  This is Neumann's "set of alternating groups occurring in the
group", in the form that the previous section can control. -/
def normalFactorSet (G : Type*) [Group G] : Set ι :=
  {i | ∃ N : Subgroup G, N.Normal ∧ Nonempty (N ≃* Q i)}

theorem mem_normalFactorSet_iff {G : Type*} [Group G] (i : ι) :
    i ∈ normalFactorSet Q G ↔ ∃ N : Subgroup G, N.Normal ∧ Nonempty (N ≃* Q i) :=
  Iff.rfl

private theorem normalFactorSet_mono {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) : normalFactorSet Q A ⊆ normalFactorSet Q B := by
  rintro i ⟨N, hN, ⟨eN⟩⟩
  exact ⟨N.map f.toMonoidHom, hN.map f.toMonoidHom f.surjective,
    ⟨(Subgroup.equivMapOfInjective N f.toMonoidHom f.injective).symm.trans eN⟩⟩

/-- **The invariant is an isomorphism invariant.**  This is what
`Sofic/ContinuumFamilyCriterion` asks a separating invariant to be. -/
theorem normalFactorSet_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    normalFactorSet Q A = normalFactorSet Q B :=
  Set.Subset.antisymm (normalFactorSet_mono Q e) (normalFactorSet_mono Q e.symm)

end Invariant

/-! ## The factors of a product, and the reverse inclusion -/

section PiFactor

variable {ι : Type u} {Q : ι → Type v} [∀ i, Group (Q i)]

/-- The `i`-th factor of a product, as a subgroup: the elements supported at
`i`. -/
def piFactor (i : ι) : Subgroup (∀ j, Q j) where
  carrier := {x | ∀ j, j ≠ i → x j = 1}
  one_mem' := by
    intro j _
    rfl
  mul_mem' := by
    intro x y hx hy j hj
    show x j * y j = 1
    rw [hx j hj, hy j hj, mul_one]
  inv_mem' := by
    intro x hx j hj
    show (x j)⁻¹ = 1
    rw [hx j hj, inv_one]

theorem mem_piFactor_iff {i : ι} {x : ∀ j, Q j} :
    x ∈ (piFactor i : Subgroup (∀ j, Q j)) ↔ ∀ j, j ≠ i → x j = 1 := Iff.rfl

/-- Each factor is normal in the product. -/
instance piFactor_normal (i : ι) : (piFactor i : Subgroup (∀ j, Q j)).Normal where
  conj_mem x hx y j hj := by
    show y j * x j * (y j)⁻¹ = 1
    simp [hx j hj]

/-- **The reverse inclusion.**  A subgroup of the product that contains the
whole `i`-th factor has a normal subgroup isomorphic to `Q i`.

"Contains the factor" is spelled as an existential rather than through
`Pi.mulSingle`, which would drag in a `DecidableEq` on the index type and make
the hypothesis's type depend on which decidability instance was in scope where
it was stated. -/
theorem exists_normal_mulEquiv_of_factor_mem
    {G : Subgroup (∀ i, Q i)} {i : ι}
    (hfac : ∀ q : Q i, ∃ g ∈ G, (∀ j, j ≠ i → g j = 1) ∧ g i = q) :
    ∃ N : Subgroup G, N.Normal ∧ Nonempty (N ≃* Q i) := by
  have hinj : Function.Injective
      ((coordHom G i).comp ((piFactor i).comap G.subtype).subtype) := by
    intro m₁ m₂ hm
    have hval : ((m₁ : G) : ∀ k, Q k) = ((m₂ : G) : ∀ k, Q k) := by
      funext j
      by_cases hj : j = i
      · subst hj
        exact hm
      · have h₁ : ((m₁ : G) : ∀ k, Q k) j = 1 := m₁.2 j hj
        have h₂ : ((m₂ : G) : ∀ k, Q k) j = 1 := m₂.2 j hj
        rw [h₁, h₂]
    exact Subtype.ext (Subtype.ext hval)
  have hsurj : Function.Surjective
      ((coordHom G i).comp ((piFactor i).comap G.subtype).subtype) := by
    intro q
    obtain ⟨g, hgG, hgsupp, hgi⟩ := hfac q
    exact ⟨⟨⟨g, hgG⟩, hgsupp⟩, hgi⟩
  exact ⟨(piFactor i).comap G.subtype,
    Subgroup.Normal.comap (piFactor_normal i) G.subtype,
    ⟨MulEquiv.ofBijective
      ((coordHom G i).comp ((piFactor i).comap G.subtype).subtype)
      ⟨hinj, hsurj⟩⟩⟩

end PiFactor

/-! ## The recovery theorem -/

section Recovery

variable {Q : ℕ → Type v} [∀ n, Group (Q n)] [∀ n, IsSimpleGroup (Q n)]

/-- **Neumann's invariant recovers the index set.**

For a subgroup `G` of the product `∏_{n ∈ S} Q n` that is subdirect and
contains every factor, with the `Q n` simple and pairwise nonisomorphic, the
isomorphism invariant `normalFactorSet Q` computes `S` on the nose.

Both inclusions are proved: `⊆` is `exists_mulEquiv_factor` (the half that had
been missing) together with pairwise nonisomorphism, and `⊇` is
`exists_normal_mulEquiv_of_factor_mem`. -/
theorem normalFactorSet_eq_of_subsetProduct
    (hpair : ∀ m n : ℕ, Nonempty (Q m ≃* Q n) → m = n)
    {S : Set ℕ} {G : Subgroup (∀ i : S, Q (i : ℕ))}
    (hG : IsSubdirect G)
    (hfac : ∀ (i : S) (q : Q (i : ℕ)), ∃ g ∈ G,
      (∀ j, j ≠ i → g j = 1) ∧ g i = q) :
    normalFactorSet Q G = S := by
  apply Set.Subset.antisymm
  · rintro m ⟨N, hN, ⟨eN⟩⟩
    obtain ⟨i, ⟨eQ⟩⟩ := exists_mulEquiv_factor hG hN eN
    have hmi : m = (i : ℕ) := hpair m (i : ℕ) ⟨eQ⟩
    rw [hmi]
    exact i.2
  · intro n hn
    -- `Q` is pinned: from `hfac ⟨n, hn⟩` alone the unifier must solve
    -- `?Q ⟨n, hn⟩ =?= Q ↑⟨n, hn⟩`, which admits the constant solution
    -- `fun _ ↦ Q n` as well as the intended `fun j ↦ Q ↑j`, and the constant
    -- one then makes the ambient `Subgroup (∀ i, ?Q i)` disagree with `G`.
    exact exists_normal_mulEquiv_of_factor_mem
      (Q := fun j : S ↦ Q (j : ℕ)) (G := G) (hfac ⟨n, hn⟩)

end Recovery

end NeumannSimpleSocle
end GroupApproximation
