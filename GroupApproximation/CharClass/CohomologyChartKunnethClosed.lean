import GroupApproximation.CharClass.CohomologyChartGenBridge
import GroupApproximation.CharClass.ProjectiveSpaceRingClosed

/-!
# The projective-factor Künneth, unconditionally

`cc-projective`'s `CPn.cpGenHyp` closes the one hypothesis the chart layer was
stated over, so every result of that layer is now a theorem with no side
conditions beyond `1 ≤ d`.  Each proof here is one application; nothing is
reproved and no cast intervenes, because `cpGenHyp` was delivered in exactly the
shape `cpSplit_of_cpGenHyp` asks for.

Note which half of the ring is used.  `cpGenHyp` is generation alone.  The
non-vanishing of the top power, `cupPowE_cpGen_ne_zero`, is never consumed on
this side, which is what the earlier reading of the circle predicted: the
hypothesis paid for flatness, and flatness needs only that a class of positive
even degree is divisible by the generator.

## Main declarations

* `KnCP.cpSplit_closed` — the product form, at every rank, over every base.
* `KnCP.flat_closed` — restrictions to the intersection are pullbacks from the
  base.
* `KnCP.mvResV_surjective_closed` — the restriction to the punctured piece is
  onto, in every degree.
* `KnCP.cpTop_cup_injective_closed` — its kernel is free of rank one on `cpTop`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-- **The product form, unconditionally.**  Every class of degree `2 + m` on
`U × ℂP^d` is a pullback from `U` plus the degree-two generator cupped with a
class of degree `m`, for every base `U` and every rank. -/
theorem cpSplit_closed (d : ℕ) (hd : 1 ≤ d) : CPSplit d :=
  cpSplit_of_cpGenHyp (fun e _ => CPn.cpGenHyp e) d hd

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **Flatness, unconditionally.**  The restriction of a class on the punctured
piece to the intersection is pulled back from the base. -/
theorem flat_closed (hd : 1 ≤ d) (k m : ℕ) (hk : 2 + m = k)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ e : Hmod2 (TopCat.of U) k,
      (mvResWV (chartU U d) (punctU U d) (cp_sup U d) k).hom w
        = pull (cpPrSub U d (interUSet U d)) k e :=
  flat_of_cpSplit U d hd (cpSplit_closed d hd) k m hk w

/-- **Surjectivity of the restriction, unconditionally and in every degree.** -/
theorem mvResV_surjective_closed (hd : 1 ≤ d) (k : ℕ)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod2 (cpProdTop U d) k,
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w :=
  mvResV_surjective_of_cpSplit_all U d hd (cpSplit_closed d hd) k w

/-- **Uniqueness of the `cpTop`-coefficient, unconditionally.**  With the previous
theorem: the restriction to the punctured piece is a split surjection whose kernel
is free of rank one on `cpTop`, at every rank and over an arbitrary base. -/
theorem cpTop_cup_injective_closed (hd : 1 ≤ d) (m : ℕ) (b : Hmod2 (TopCat.of U) m)
    (h : cup (cpTop U d) (pull (cpPrU U d) m b) = 0) : b = 0 :=
  cpTop_cup_injective U d hd (cpSplit_closed d hd) m b h

end KnCP

end

end GroupApproximation.CharClass
