import GroupApproximation.CharClass.CupVanishCochain
import GroupApproximation.CharClass.CupVanishSmallAnn
import GroupApproximation.CharClass.CartanCoverRep

/-!
# Classes vanishing on the two halves of a cover have vanishing product

The three pieces are in place, so this is their composition and nothing else.

`cc-cartan`'s `exists_cocycle_vanishing_on` supplies, for each factor, a cocycle
representative that vanishes on every simplex lying in its own open set.
`cochainCup_mem_smallAnn` says their cup product then kills every simplex small
for the two-member cover.  `cocycleClass_eq_zero_of_mem_smallAnn` says such a
cocycle has zero class.  `cup_mk` says the class of the cochain cup is the cup of
the classes.

Both degrees stay free with one positivity hypothesis.  Writing the second degree
as a successor instead looks equivalent and is not: the product then has degree
`p + (q + 1)` where the small-chain step wants `(p + q) + 1`, and although those
are definitionally equal, closing across them with `exact` sends `isDefEq` through
the whole cochain structure and times out.  The successor is destructured inside
`cocycleClass_eq_zero_of_mem_smallAnn_pos`, where the degree is a variable and
`subst` applies.

## Main declarations

* `cocycleClass_eq_zero_of_mem_smallAnn_pos` — the small-chain step at a positive
  degree.
* `cup_eq_zero_of_absToSub_eq_zero` — **the two-set theorem.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- The small-chain step at a degree that is only known to be positive.  The
successor is destructured **here**, where the degree is a variable and `subst`
applies, rather than at the call site, where it would be a compound term and the
defeq check between `p + (q + 1)` and `(p + q) + 1` runs `isDefEq` through the
whole cochain structure. -/
theorem cocycleClass_eq_zero_of_mem_smallAnn_pos (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (m : ℕ) (hm : 0 < m)
    (φ : singularCochainGroup (ZMod 2) X m)
    (hmem : φ ∈ smallAnnSubmodule (ZMod 2) X 𝒰 m)
    (hφ : cochainCoboundary (ZMod 2) X m φ = 0) :
    cocycleClass X m φ hφ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact cocycleClass_eq_zero_of_mem_smallAnn X 𝒰 n φ hmem hφ

/-- **The two-set theorem.**  If `a` restricts to zero on `U`, `b` restricts to
zero on `V`, and `U` and `V` cover, then `a ⌣ b = 0`.

The hypotheses are stated with `absToSub`, which is the shape
`exists_cocycle_vanishing_on` consumes and, by `absToSub_eq_cohPullback`, the
cohomology pullback along the inclusion of the subspace.  Both degrees stay free
with a single positivity hypothesis, so every degree in the proof is the same
term `p + q` and nothing is ever checked for definitional equality across two
spellings. -/
theorem cup_eq_zero_of_absToSub_eq_zero (U V : Opens X) (hUV : U ⊔ V = ⊤)
    {p q : ℕ} (hpq : 0 < p + q) (a : Hmod2 X p) (b : Hmod2 X q)
    (ha : (absToSub (ZMod 2) (U : Set X) p).hom a = 0)
    (hb : (absToSub (ZMod 2) (V : Set X) q).hom b = 0) :
    cup a b = 0 := by
  obtain ⟨α, hαmem, hαc, rfl⟩ := exists_cocycle_vanishing_on X (U : Set X) p a ha
  obtain ⟨β, hβmem, hβc, rfl⟩ := exists_cocycle_vanishing_on X (V : Set X) q b hb
  rw [cup_mk]
  exact cocycleClass_eq_zero_of_mem_smallAnn_pos X (twoSetCover U V hUV) (p + q) hpq
    (cochainCup p q α β) (cochainCup_mem_smallAnn U V hUV hαmem hβmem) _

end

end GroupApproximation.CharClass
