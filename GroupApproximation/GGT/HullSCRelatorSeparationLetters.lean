import GroupApproximation.GGT.HullSCRelatorSeparationBlock

/-!
# The letters of Hull's relator are rigid

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii.

Once the blocks of a matched prefix are aligned one to one
(`GGT/HullSCRelatorSeparationBlock.lean`), the alignment has to be turned into
an equality of *rotation indices*: that is Olshanskii's step from "the blocks
correspond" to "the two members of the symmetrized closure are the same word up
to a translation".  The mechanism is that a block letter of the relator occurs
exactly once, so its position is determined by the letter, so a correspondence
between blocks is a correspondence between positions.

This module proves the letter half of that.

* `base_ne_comp`, `notMem_map_base_of_comp` -- the base part of the relator
  contains no block letter, the two being different constructors of
  `GGT.RelLetter`.  So every occurrence of a block letter is in the block part.
* `exponent_eq_of_pow_eq` -- a power of the loxodromic determines its exponent,
  the element having infinite order.
* `nodup_blockLetters` -- with the exponents chosen without repetition
  (`HullSC.exists_separated_relator_exponents` supplies `ms.Nodup`), the block
  letters of the relator are pairwise distinct.

Together these say that the block letters of the relator are a repetition-free
list disjoint from the base part, which is what makes a block letter name its
own position.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Letters

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **A base letter is never a block letter.**  They are different constructors
of `GGT.RelLetter`, and that disjointness is the point of the type: the same
group element occurring as a base letter and as a component letter labels
different edges of `Γ(G, X ⊔ ⨆H)`. -/
theorem base_ne_comp (g h : G) (lam : Λ) :
    (GGT.RelLetter.base g : GGT.RelLetter G Λ) ≠ GGT.RelLetter.comp lam h := by
  intro hc
  simp at hc

omit [Group G] in
/-- **The base part of the relator contains no block letter.**  So every
occurrence of a block letter in the relator is an occurrence in the run of
powers. -/
theorem notMem_map_base_of_comp (l : List G) (lam : Λ) (h : G) :
    (GGT.RelLetter.comp lam h : GGT.RelLetter G Λ)
      ∉ l.map GGT.RelLetter.base := by
  intro hmem
  obtain ⟨g, -, hg⟩ := List.mem_map.mp hmem
  exact base_ne_comp g h lam hg

end Letters

/-! ## Blocks of Hull's relator -/

section Blocks

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **A power of the loxodromic determines its exponent**, the element having
infinite order because it is loxodromic. -/
theorem exponent_eq_of_pow_eq (E : HypEmbeddedCore A N) {m m' : ℕ}
    (h : E.lox ^ m = E.lox ^ m') : m = m' :=
  injective_pow_of_not_isOfFinOrder
    (not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic) h

/-- **A block letter determines its exponent.**  This is
`exponent_eq_of_comp_eq` read as injectivity of the map that builds the block
letters, which is what `List.Nodup.map` consumes. -/
theorem injective_blockLetter (E : HypEmbeddedCore A N) :
    Function.Injective
      (fun m : ℕ => (GGT.RelLetter.comp () (E.lox ^ m) : GGT.RelLetter G Unit)) :=
  fun _ _ h => exponent_eq_of_comp_eq E h

/-- **The block letters of the relator are pairwise distinct**, the exponents
being pairwise distinct and a block letter determining its exponent.

`HullSC.exists_separated_relator_exponents` supplies the `Nodup` hypothesis at
every length, so this costs the design nothing. -/
theorem nodup_blockLetters (E : HypEmbeddedCore A N) {ms : List ℕ}
    (hnodup : ms.Nodup) :
    (ms.map fun m =>
      (GGT.RelLetter.comp () (E.lox ^ m) : GGT.RelLetter G Unit)).Nodup :=
  List.Nodup.map (injective_blockLetter E) hnodup

/-- **A block letter of the relator occurs only in its block part.**  Combining
the two halves: an occurrence of `comp () (h^m)` in `relatorWord p h ms` is an
occurrence of `m` in `ms`. -/
theorem mem_of_comp_mem_relatorWord (E : HypEmbeddedCore A N) {p : List G}
    {ms : List ℕ} {m : ℕ}
    (hmem : (GGT.RelLetter.comp () (E.lox ^ m) : GGT.RelLetter G Unit)
      ∈ relatorWord p E.lox ms) : m ∈ ms := by
  rcases mem_relatorWord hmem with ⟨g, -, hg⟩ | ⟨m', hm', hm'eq⟩
  · exact absurd hg.symm (base_ne_comp g (E.lox ^ m) ())
  · rw [exponent_eq_of_comp_eq E hm'eq]
    exact hm'

end Blocks

end HullSC
end GroupApproximation
