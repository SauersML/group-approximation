import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.Kazhdan.CCKWCosetComplex

/-!
# Typed link largeness of the coset complex of `GHB(7)`

The coset complex of `GHB(7)` (`Kazhdan/CCKWCosetComplex.lean`) has large links in the typed
sense of `Systolic.LinksLargeAt`: no link cycle of length below `6` at the vertices of type `0`
(cosets of `⟨a,b⟩ ≅ U₃(7)`), and none below `8` at the vertices of types `1` and `2` (cosets of
`⟨c,b⟩` and `⟨c,a⟩ ≅ U₄(7)`).  In particular its links are 6-large.  Both statements take the
order bounds `|U₃(7)| ≤ 7³`, `|U₄(7)| ≤ 7⁴` of CCKW Proposition 7.2.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- **Typed link largeness of the coset complex of `GHB(7)`**: girth `6` at type `0`, `8` at
types `1` and `2`. -/
theorem cosetComplex_linksLargeAt [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    Systolic.LinksLargeAt cosetComplex (fun x => if x.1 = 0 then 6 else 8) :=
  fun v c h3c hlt hnd hadj => cosetComplex_linkCycles h3 h4 v c h3c hlt hnd hadj

/-- **The links of the coset complex of `GHB(7)` are 6-large.** -/
theorem cosetComplex_linksSixLarge [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    Systolic.LinksSixLarge cosetComplex :=
  Systolic.linksSixLarge_of_linksLargeAt (cosetComplex_linksLargeAt h3 h4) fun v => by
    show 6 ≤ if v.1 = 0 then 6 else 8
    split <;> omega

end CCKW
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetComplex_linksLargeAt
#audit_axioms GroupApproximation.KMSGroup.CCKW.cosetComplex_linksSixLarge
