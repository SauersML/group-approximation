import GroupApproximation.GGT.HullSCRelatorSeparation2Rigid

/-!
# The two-subgroup core Hull's §6 actually runs over

`HullSC.HypEmbeddedCore` carries one hyperbolically embedded subgroup and
`Λ = Unit`, and `GGT/HullSCRelatorSeparationNotQG.lean` shows that model cannot
carry a quasi-geodesic relator: the `H`-letters merge into one component
spanning a single edge.  Hull's own relator is built from **independent**
loxodromic elements, which is to say from two members of the family, so the
faithful structure carries both.

What it does NOT carry is the independence clause itself.  Nothing in the chain
consumes it --- the relator's alternation is syntactic, `blockWord` labelling
consecutive letters with opposite indices whatever the two elements are --- and
what the clause was kept for, excluding the degenerate pair `H false = H true`,
Hull's (W4) does more sharply: `HullSC.H_ne_of_disjoint₂` derives it from the
disjointness and a loxodromic element being nontrivial.

`HypEmbeddedCore₂` is that structure, and the lemmas here are what the relator
built on it needs: what it names, what its letters are, and that the element it
spells beyond `t⁻¹` lies in `N`.

The `Λ = Unit` core is left alone; nothing here changes it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The two hyperbolically embedded subgroups Hull's relator alternates
between**, over Hull's own alphabet, with the two loxodromic elements whose
powers are the relator's letters. -/
structure HypEmbeddedCore₂ {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) where
  /-- The relative generating set, with Hull's alphabet as its base. -/
  rel : GGT.RelGenSet G Bool
  /-- Its base is Hull's alphabet. -/
  base_eq : rel.base = A.alphabet.carrier
  /-- The two hyperbolically embedded subgroups. -/
  H : Bool → Subgroup G
  /-- They are the family of `rel`. -/
  fam_eq : rel.fam = H
  /-- Both lie inside the suitable subgroup, so the relator's letters do. -/
  le : ∀ b : Bool, H b ≤ N
  /-- `{H₀, H₁} ↪_h (G, A)`. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The elements whose powers are the relator's letters. -/
  lox : Bool → G
  /-- Each lies in its own subgroup. -/
  lox_mem : ∀ b : Bool, lox b ∈ H b
  /-- Each is loxodromic on `Γ(G,A)`. -/
  lox_isLoxodromic : ∀ b : Bool, IsLoxodromic (lox b) (Cayley.base A.alphabet)
  /-- **Hull's (W4): the two subgroups meet trivially.**

  In Hull's §5 this is not an assumption but a consequence: Corollary 5.7 gives
  `E(hᵢ) = ⟨hᵢ⟩` for the suitable powers, independence separates the two cyclic
  groups, and Dahmani--Guirardel--Osin's 6.8 and 6.14 make `E(h₀) ∩ E(h₁)`
  finite --- which is trivial in the torsion-free ambient this programme
  studies.  That derivation is not in this repository; the clause is recorded
  here as an input.

  It is what makes the aligned case's second connector trivial.  Without it the
  chain excluded the diagonal by a design clause about commutation, which
  `GGT/HullSCRelatorSeparation2ApplyLoxGap.lean` shows cannot be discharged at
  this core --- and which Hull never needs, because his pieces exclude the
  conjugacy identity syntactically. -/
  disjoint : ∀ x : G, x ∈ H false → x ∈ H true → x = 1

section Core

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- The base of the two-subgroup core is a symmetric generating set. -/
theorem isSymmetricGeneratingSet_base₂ (E : HypEmbeddedCore₂ A N) :
    IsSymmetricGeneratingSet E.rel.base := by
  rw [E.base_eq]
  exact A.alphabet.symmetricGenerating

/-- The powers of each of the two elements are all distinct. -/
theorem injective_pow_lox₂ (E : HypEmbeddedCore₂ A N) (b : Bool) :
    Function.Injective (fun n : ℕ => E.lox b ^ n) :=
  injective_pow_of_not_isOfFinOrder
    (not_isOfFinOrder_of_isLoxodromic (E.lox_isLoxodromic b))

/-- **The two subgroups are distinct**, which is what the independence clause
used to be kept for and what (W4) gives outright: were they equal, the first
loxodromic element would lie in both, so `disjoint` would make it trivial, and a
loxodromic element has infinite order. -/
theorem H_ne_of_disjoint₂ (E : HypEmbeddedCore₂ A N) : E.H false ≠ E.H true := by
  intro hEq
  have hmem : E.lox false ∈ E.H true := by
    rw [← hEq]
    exact E.lox_mem false
  have h1 : E.lox false = 1 := E.disjoint _ (E.lox_mem false) hmem
  refine not_isOfFinOrder_of_isLoxodromic (E.lox_isLoxodromic false) ?_
  rw [h1]
  exact IsOfFinOrder.one

end Core

section Word

variable {G : Type u} [Group G]

/-- **What the relator names**: the base spelling followed by the alternating
run. -/
theorem listVal_relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) :
    GGT.RelLetter.listVal (relatorWord₂ p h₀ h₁ ms)
      = p.prod * GGT.RelLetter.listVal (blockWord h₀ h₁ false ms) := by
  show GGT.RelLetter.listVal
      (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms) = _
  rw [RelWord.listVal_append, listVal_map_base]

/-- **The letters of the relator**: a base letter of `p`, or a power of one of
the two elements. -/
theorem mem_relatorWord₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {x : GGT.RelLetter G Bool} (hx : x ∈ relatorWord₂ p h₀ h₁ ms) :
    (∃ g ∈ p, x = GGT.RelLetter.base g) ∨
      (∃ (b : Bool) (m : ℕ), m ∈ ms ∧
        x = GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ m)) := by
  have hx' : x ∈ p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms := hx
  rcases List.mem_append.mp hx' with h | h
  · obtain ⟨g, hg, hgx⟩ := List.mem_map.mp h
    exact Or.inl ⟨g, hg, hgx.symm⟩
  · obtain ⟨b, m, hm, hxeq⟩ := mem_blockWord h₀ h₁ false ms x h
    exact Or.inr ⟨b, m, hm, hxeq⟩

/-- **The run names an element of `N`**, its letters being powers of elements of
two subgroups of `N`.  This is Hull's `u`, and as over one subgroup it is not a
choice: the relator's shape produces it. -/
theorem listVal_blockWord_mem {N : Subgroup G} {h₀ h₁ : G}
    {K : Bool → Subgroup G} (hle : ∀ b : Bool, K b ≤ N)
    (hmem : ∀ b : Bool, (if b then h₁ else h₀) ∈ K b) :
    ∀ (b : Bool) (ms : List ℕ),
      GGT.RelLetter.listVal (blockWord h₀ h₁ b ms) ∈ N := by
  intro b ms
  induction ms generalizing b with
  | nil =>
      rw [blockWord_nil, GGT.RelLetter.listVal_nil]
      exact one_mem N
  | cons m t ih =>
      rw [blockWord_cons, RelWord.listVal_cons]
      refine mul_mem ?_ (ih (!b))
      show (if b then h₁ else h₀) ^ m ∈ N
      exact hle b (pow_mem (hmem b) m)

end Word

end HullSC
end GroupApproximation
