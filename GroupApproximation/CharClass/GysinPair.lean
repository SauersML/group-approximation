import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# Where the intersection is acyclic, the pair of restrictions is bijective

The Gysin step reads the cohomology of the projectivised sum through the two
pieces of its cover, and that reading is faithful exactly where the intersection,
the sphere bundle, has no cohomology.  This file is that statement and nothing
else: it is two lines of the Mayer–Vietoris sequence and uses no bundle data, no
retraction and no Leray–Hirsch.

Injectivity is exactness at the ambient space, where a class killed by both
restrictions comes from the intersection one degree down.  Surjectivity is
exactness in the middle, where a pair is in the image as soon as its two
restrictions to the intersection agree, and in a zero group they do.

## Main declarations

* `bijective_resPair` — **the pair of restrictions is bijective** in a degree
  where the intersection vanishes in that degree and the one below.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory

noncomputable section

variable {X U V W : TopCat.{0}}

/-- **The pair of restrictions is bijective where the intersection is acyclic.**
Both halves are one line of Mayer–Vietoris: a class killed by both restrictions
comes from the intersection one degree down, and a pair is in the image as soon as
its two restrictions to the intersection agree, which in a zero group is
automatic. -/
theorem bijective_resPair (mv : MVSequence X U V W) (n : ℕ)
    (hWn : ∀ w : Hmod2 W n, w = 0) (hWn1 : ∀ w : Hmod2 W (n + 1), w = 0) :
    Function.Bijective
      (fun z : Hmod2 X (n + 1) => (mv.resU (n + 1) z, mv.resV (n + 1) z)) := by
  constructor
  · have hzero : ∀ z : Hmod2 X (n + 1),
        mv.resU (n + 1) z = 0 → mv.resV (n + 1) z = 0 → z = 0 := by
      intro z hU hV
      obtain ⟨w, hw⟩ := (mv.exact_X n z).mp ⟨hU, hV⟩
      rw [← hw, hWn w, map_zero]
    intro z z' h
    have hu : mv.resU (n + 1) z = mv.resU (n + 1) z' := congrArg Prod.fst h
    have hv : mv.resV (n + 1) z = mv.resV (n + 1) z' := congrArg Prod.snd h
    have hU : mv.resU (n + 1) (z - z') = 0 := by rw [map_sub, hu, sub_self]
    have hV : mv.resV (n + 1) (z - z') = 0 := by rw [map_sub, hv, sub_self]
    exact sub_eq_zero.mp (hzero _ hU hV)
  · intro ab
    obtain ⟨z, hzU, hzV⟩ :=
      (mv.exact_sum (n + 1) ab.1 ab.2).mp
        ((hWn1 _).trans (hWn1 _).symm)
    exact ⟨z, by
      show (mv.resU (n + 1) z, mv.resV (n + 1) z) = ab
      rw [hzU, hzV]⟩

end

end Gysin
end CharClass
end GroupApproximation
