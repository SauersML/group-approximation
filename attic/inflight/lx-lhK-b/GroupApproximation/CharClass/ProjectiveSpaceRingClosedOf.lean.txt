import GroupApproximation.CharClass.ProjectiveSpaceRingBootstrapOf
import GroupApproximation.CharClass.LerayHirschProductOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The powers of a degree-two class of `ℂP^d` over a field are nonzero, unconditionally

`ProjectiveSpaceRingBootstrapOf.cupPowE_ne_zeroOf_of_freeTuple` asks for one input, the free tuple of
`U × ℂP^1` with a nonzero fibre class, and `LerayHirschProductOf.hasFreeTuple_cpProd_zeroOf` supplies it
with no hypothesis (rank two needs no ring: the only power in range is the class itself).  So the ring
input of the general-rank Leray–Hirsch ladder over `K` holds outright.

## Main declarations

* `cupPowE_ne_zeroOf` — **every nonzero `h ∈ H^2(ℂP^d; K)` has `h^m ≠ 0` for `m ≤ d`**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory

noncomputable section

/-- **Every nonzero degree-two class of `ℂP^d` has nonzero powers up to the dimension**, over any
field, with no hypothesis. -/
theorem cupPowE_ne_zeroOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2)
    (h0 : h ≠ 0) {m : ℕ} (hm : m ≤ d) : cupPowE h m ≠ 0 :=
  cupPowE_ne_zeroOf_of_freeTuple K
    (by
      intro U _ hfib hfib0
      exact LH.hasFreeTuple_cpProd_zeroOf K U hfib hfib0)
    d hd h h0 hm

end

#audit_axioms cupPowE_ne_zeroOf

end CPn
end CharClass
end GroupApproximation
