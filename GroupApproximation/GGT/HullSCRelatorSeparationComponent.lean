import GroupApproximation.GGT.HullSCRelatorSeparationLetters
import GroupApproximation.GGT.OsinComponents

/-!
# Hull's relator has one `H`-component, not one per exponent

Osin, *Acylindrically hyperbolic groups*, Definition 4.1: an `H_λ`-component of
a path is a **maximal run** of `λ`-letters.

`HullSC.relatorWord p h ms` is `p.map base ++ ms.map (fun m => comp () (h ^ m))`,
so its `H`-letters are consecutive and all carry the single index `()`.  They are
therefore one component, spanning `h^{Σ mᵢ}` -- not `ms.length` components
spanning the individual `h^{mᵢ}`.

That is what `isComp_relatorWord` proves, and it is a correction to the
granularity at which the polygon lemma can be applied: the isolated-component
bound sees the run, and the individual exponents are invisible to it.  The
letters inside a run are still letters, and
`GGT.OsinComponents.vertex` still walks through them, but "component" in Osin's
sense means the whole run.

Two consequences.

* A separation design that separates the individual exponents
  (`HullSC.exists_separated_relator_exponents`) is aimed below the granularity
  the geometry delivers.  What a matched component supplies is an equation
  between the elements two *runs* span, so the quantity to separate is the sum
  over a run, not the individual exponent.
* A rotation of the relator has at most two runs -- the tail of the run and its
  head, with the base part `p` between them -- so a prefix of a member of the
  symmetrized closure carries at most two components.  That is what makes the
  self-connection question concrete: the two runs of one rotation are separated
  by the whole of `p`, and `p` may be taken long
  (`HullSC.exists_long_base_spelling`).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Component

variable {G : Type u} [Group G]

omit [Group G] in
/-- A component letter carries its own index. -/
theorem isCompOf_comp {Λ : Type*} (lam : Λ) (h : G) :
    (GGT.RelLetter.comp lam h : GGT.RelLetter G Λ).IsCompOf lam := rfl

omit [Group G] in
/-- A base letter carries no index. -/
theorem not_isCompOf_base {Λ : Type*} (lam : Λ) (g : G) :
    ¬ (GGT.RelLetter.base g : GGT.RelLetter G Λ).IsCompOf lam := fun h => h

/-- **A letter of the relator below `|p|` is a base letter**, so it is not a
letter of the component. -/
theorem not_isCompOf_getElem_relatorWord {p : List G} {a : G} {ms : List ℕ}
    {j : ℕ} (hj : j < p.length) (hjv : j < (relatorWord p a ms).length) :
    ¬ ((relatorWord p a ms)[j]'hjv).IsCompOf () := by
  have hv : relatorWord p a ms
      = p.map GGT.RelLetter.base
        ++ ms.map (fun r => GGT.RelLetter.comp () (a ^ r)) := rfl
  have h1 : (relatorWord p a ms)[j]? = (p.map GGT.RelLetter.base)[j]? := by
    rw [hv]
    exact List.getElem?_append_left (by rwa [List.length_map])
  have h2 : (relatorWord p a ms)[j]'hjv ∈ p.map GGT.RelLetter.base := by
    refine List.mem_of_getElem? (i := j) ?_
    rw [← h1]
    exact List.getElem?_eq_getElem hjv
  obtain ⟨g, -, hg⟩ := List.mem_map.mp h2
  exact hg ▸ not_isCompOf_base () g

/-- **A letter of the relator at or above `|p|` is a letter of the component.**
Every one of them carries the single index `()`, so the whole run is one
component. -/
theorem isCompOf_getElem_relatorWord {p : List G} {a : G} {ms : List ℕ} {j : ℕ}
    (hj : p.length ≤ j) (hjv : j < (relatorWord p a ms).length) :
    ((relatorWord p a ms)[j]'hjv).IsCompOf () := by
  have hv : relatorWord p a ms
      = p.map GGT.RelLetter.base
        ++ ms.map (fun r => GGT.RelLetter.comp () (a ^ r)) := rfl
  have h1 : (relatorWord p a ms)[j]?
      = (ms.map (fun r => GGT.RelLetter.comp () (a ^ r)))[j - p.length]? := by
    rw [hv, List.getElem?_append_right (by rwa [List.length_map]),
      List.length_map]
  have h2 : (relatorWord p a ms)[j]'hjv
      ∈ ms.map (fun r => GGT.RelLetter.comp () (a ^ r)) := by
    refine List.mem_of_getElem? (i := j - p.length) ?_
    rw [← h1]
    exact List.getElem?_eq_getElem hjv
  obtain ⟨r, -, hr⟩ := List.mem_map.mp h2
  exact hr ▸ isCompOf_comp () (a ^ r)

/-- **The `H`-letters of Hull's relator form a single component.**

Osin's components are maximal runs of letters of one index, and the relator
puts all its `H`-letters consecutively at the end with the single index `()`.
So the component is `[|p|, |p| + |ms|)` and it spans `h^{Σ mᵢ}`, whatever the
individual exponents are.

The consequence for Olshanskii's separation is that the polygon lemma matches
runs, not exponents. -/
theorem isComp_relatorWord {p : List G} {a : G} {ms : List ℕ} (hms : ms ≠ []) :
    GGT.OsinComponents.IsComp () (relatorWord p a ms) p.length
      (p.length + ms.length) := by
  have hpos : 0 < ms.length :=
    Nat.pos_of_ne_zero (fun h0 => hms (List.length_eq_zero_iff.mp h0))
  refine ⟨by omega, le_of_eq (length_relatorWord p a ms).symm, ?_, ?_, ?_⟩
  · intro j hj1 _ hjv
    exact isCompOf_getElem_relatorWord hj1 hjv
  · intro j hje hjv
    exact not_isCompOf_getElem_relatorWord (by omega) hjv
  · intro hk
    rw [length_relatorWord] at hk
    omega

end Component

end HullSC
end GroupApproximation
