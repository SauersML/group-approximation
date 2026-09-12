import GroupApproximation.GGT.DGOProposition435InclusionFinite

/-!
# The joint family read over the auxiliary base

`DGOProposition435JointHyperbolicStatement` is the last input of the nested
form of Proposition 4.35.  It disappears when the original peripheral family is
read over the *auxiliary* base rather than over its own.

`originalOverAux D E` is that reading: the original family with its base
replaced by the auxiliary base minus the original peripherals.  Its alphabet is
the auxiliary base on the nose (`originalOverAux_alphabet_carrier`), so the
joint alphabet built from it is *literally* the auxiliary alphabet, and clause
(a) of hyperbolic embeddedness is inherited with no transport and no finiteness
hypothesis whatever the distance between the two bases
(`jointHyperbolic_originalOverAux`).

What the reading costs is that the original family must be hyperbolically
embedded over the auxiliary base, not merely over its own.  That is
`isHyperbolicallyEmbedded_originalOverAux`, split here into its two clauses:
clause (a) is hyperbolicity of the Cayley graph of the auxiliary base alone,
which the filling lane has for free because that base is Hull's alphabet; and
clause (b) is `DGOProposition435FullOriginalLocalFinitenessStatement`, the
local finiteness of the original peripheral metrics over Hull's alphabet.  So
the trade is a hyperbolicity input for a local-finiteness input about the
original family alone, with no auxiliary family and no joint index in it.

The auxiliary family may be taken before its relative generating set was
enlarged: only its family and its base enter, so Osin's Theorem 5.4 plays no
part.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G] {Λ : Type v} {I : Type w}

/-! ## Clause (a) for the original family over the auxiliary base -/

/-- Hyperbolicity of the Cayley graph of the auxiliary base is clause (a) for
the original family read over it. -/
theorem hyperbolic_originalOverAux_of_base (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) (Y : Alphabet G)
    (hY : Y.carrier = E.base)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley Y)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (originalOverAux D E hbase hEinv).alphabet) := by
  refine exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq ?_) hhyp
  rw [originalOverAux_alphabet_carrier, hY]

/-- The two clauses of hyperbolic embeddedness for the original family read
over the auxiliary base. -/
theorem isHyperbolicallyEmbedded_originalOverAux (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (originalOverAux D E hbase hEinv).alphabet))
    (hloc : ∀ (lam : Λ) (n : ℕ),
      ((originalOverAux D E hbase hEinv).relBall lam n).Finite) :
    (originalOverAux D E hbase hEinv).IsHyperbolicallyEmbedded :=
  ⟨hhyp, hloc⟩

/-! ## The joint family, with no hyperbolicity input -/

/-- **The joint family over the auxiliary base is hyperbolically embedded**,
from Proposition 4.14 alone.

Clause (a) is free because the joint alphabet is the auxiliary alphabet.
Clause (b) at an auxiliary index comes from the auxiliary family itself, and at
an original index from Proposition 4.14 together with the isolated-witness
statement, which is a theorem.  So the only inputs left are Proposition 4.14
and the hyperbolic embeddedness of the original family over the auxiliary
base. -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_originalOverAux
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    [Finite I] (D : RelGenSet G Λ) (E E' : RelGenSet G I)
    (hfam : E'.fam = E.fam) (hbase : D.alphabet.carrier ⊆ E'.base)
    (hEinv : ∀ x ∈ E'.base, x⁻¹ ∈ E'.base) (hsub : E'.base ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hDhull : (originalOverAux D E' hbase hEinv).IsHyperbolicallyEmbedded)
    (hE' : E'.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSet (originalOverAux D E' hbase hEinv)
      E).IsHyperbolicallyEmbedded :=
  isHyperbolicallyEmbedded_jointRelGenSet_of_proposition414Uniform h414
    dgoProposition435IsolatedWitness (originalOverAux D E' hbase hEinv) E
    (by
      rw [originalOverAux_alphabet_carrier]
      exact hsub)
    hEsymm hDhull hE
    (jointHyperbolic_originalOverAux D E E' hfam hbase hEinv hE'.hyperbolic)

/-- The same with the auxiliary family taken to be the one it is read over, the
case the filling lane uses when the family is not enlarged. -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_originalOverAux_self
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base)
    (hDhull : (originalOverAux D E hbase hEinv).IsHyperbolicallyEmbedded)
    (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSet (originalOverAux D E hbase hEinv)
      E).IsHyperbolicallyEmbedded :=
  isHyperbolicallyEmbedded_jointRelGenSet_originalOverAux h414 D E E rfl hbase
    hEinv Set.Subset.rfl hEinv hDhull hE hE

end RelHyp
end GGT
end GroupApproximation
