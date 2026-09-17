import GroupApproximation.BooneHigman.Metabelian.ChainHost
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsStatement
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton, part 2: linear groups in positive characteristic

Research node `char-p-linear-groups-satisfy-permutational-boone-higman`, route
`char-p-linear-pbh-via-polynomial-self-similar-hosts`.  With `R_k = F_p[s_0, ..., s_{k-1}]`:

1. (`char-p-linear-groups-embed-in-polynomial-f-p-groups`, lane `bh-met-03`, imported from
   `CharPCoordsStatement.lean`) a finitely generated `H ≤ GL_n(K)`, `char K = p > 0`, embeds in
   `GL_M(R_k)`;
2. (`CharPElementaryAbsorptionStatement`, no owning lane) `GL_M(R) ↪ E_N(R)` for `N ≥ 3`,
   `N ≥ 2M`, through `g ↦ diag(g, g⁻ᵀ, 1)`, which lies in `SL_N(R) = E_N(R)` (Suslin);
3. (`CharPElementaryFPStatement`, research node `elementary-groups-over-polynomial-f-p-rings-are-fp`,
   lane `bh-met-06`) `E_N(R_k)` is finitely presented for `N ≥ k + 4` (weaker than the node's
   `N ≥ max(4, k + 3)`);
4. (`AffineExtensionFPStatement`, lane `bh-met-05`, in `ChainHost.lean`) the affine host
   `R^N ⋊ E_N(R)` is finitely presented;
5. (`CharPAffineSelfSimilarStatement`, research node
   `positive-char-polynomial-affine-groups-are-self-similar`, lane `bh-met-02`) the affine host over
   `R_k`, `k ≥ 1`, acts faithfully and self-similarly on a regular rooted tree.

To meet the hypothesis `k ≥ 1` of step 5, the coordinates of step 1 are first moved from `R_k` to
`R_{k+1}` along `s_i ↦ s_i` (`glLift`).  The permutational Boone–Higman class `B_A` of the research
node is replaced by `Products.EmbedsInFPSelfSimilarGroup`, so the node
`fp-self-similar-subgroups-satisfy-permutational-boone-higman` becomes the proved
`Products.embedsInFPSelfSimilarGroup_of_rep` (and later the envelope statement of lane `bh-met-07`).
Endpoint: `charPLinearHostStatement_of_chain`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The polynomial ring `F_p[s_0, ..., s_{k-1}]`. -/
abbrev CharPPoly (p k : ℕ) : Type := MvPolynomial (Fin k) (ZMod p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharPPoly

/-- **Absorption into the elementary group** (no owning lane).  For `N ≥ 3` and `N ≥ 2M`,
`GL_M(F_p[s])` embeds in `E_N(F_p[s])`: `g ↦ diag(g, g⁻ᵀ, 1)` is an injective homomorphism into
`SL_N`, and `SL_N(F_p[s_0, ..., s_{k-1}]) = E_N` for `N ≥ 3` by Suslin's theorem. -/
def CharPElementaryAbsorptionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k M N : ℕ), 3 ≤ N → 2 * M ≤ N →
    ∃ f : Matrix.GeneralLinearGroup (Fin M) (CharPPoly p k) →*
        elementaryGroup (Fin N) (CharPPoly p k),
      Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharPElementaryAbsorptionStatement

/-- **Research node `elementary-groups-over-polynomial-f-p-rings-are-fp`** (lane `bh-met-06`;
restated here since no such interface was on disk): `E_N(F_p[s_0, ..., s_{k-1}])` is finitely
presented for `N ≥ k + 4`. -/
def CharPElementaryFPStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), k + 4 ≤ N →
    Group.IsFinitelyPresented (elementaryGroup (Fin N) (CharPPoly p k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharPElementaryFPStatement

/-- **Research node `positive-char-polynomial-affine-groups-are-self-similar`** (lane `bh-met-02`;
restated here since no such interface was on disk): for `k ≥ 1` and `n ≥ 1`, the affine host
`F_p[s]^n ⋊ E_n(F_p[s])` acts faithfully and self-similarly on the tree over a finite alphabet
with at least two letters. -/
def CharPAffineSelfSimilarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k n : ℕ), 1 ≤ k → 1 ≤ n →
    ∃ (X : Type) (_ : Finite X) (_ : Nontrivial X)
      (ρ : AffineElementaryGroup n (CharPPoly p k) →* Trees.TreeAut X), Trees.IsSelfSimilarRep ρ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharPAffineSelfSimilarStatement

/-- **Research node `char-p-linear-groups-satisfy-permutational-boone-higman`**, with `B_A`
replaced by `Products.EmbedsInFPSelfSimilarGroup`: every finitely generated subgroup of `GL_n(K)`,
`char K = p > 0`, embeds in a finitely presented self-similar group. -/
def CharPLinearHostStatement : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 0 < p → ringChar K = p →
    ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      Products.EmbedsInFPSelfSimilarGroup H

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharPLinearHostStatement

/-- Adding one variable: `GL_M(F_p[s_0, ..., s_{k-1}]) → GL_M(F_p[s_0, ..., s_k])`. -/
noncomputable def glLift (p k M : ℕ) :
    Matrix.GeneralLinearGroup (Fin M) (CharPPoly p k) →*
      Matrix.GeneralLinearGroup (Fin M) (CharPPoly p (k + 1)) :=
  Matrix.GeneralLinearGroup.map
    (MvPolynomial.rename (R := ZMod p) (Fin.castSucc : Fin k → Fin (k + 1))).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.glLift

theorem glLift_injective (p k M : ℕ) : Function.Injective (glLift p k M) :=
  Coordinates.glMap_injective
    (f := (MvPolynomial.rename (R := ZMod p) (Fin.castSucc : Fin k → Fin (k + 1))).toRingHom)
    (MvPolynomial.rename_injective (R := ZMod p) (Fin.castSucc : Fin k → Fin (k + 1))
      (Fin.castSucc_injective k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.glLift_injective

/-- `F_p[s_0, ..., s_{k-1}]` is a quotient of `ℤ[s_0, ..., s_{k-1}]`. -/
theorem charPPoly_map_surjective (p k : ℕ) :
    Function.Surjective (MvPolynomial.map (σ := Fin k) (Int.castRingHom (ZMod p))) :=
  MvPolynomial.map_surjective _ (ZMod.ringHom_surjective _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.charPPoly_map_surjective

/-- **Composition for the positive-characteristic node.** -/
theorem charPLinearHostStatement_of_chain
    (hcoord : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habs : CharPElementaryAbsorptionStatement) (hfp : CharPElementaryFPStatement)
    (haff : AffineExtensionFPStatement) (hss : CharPAffineSelfSimilarStatement) :
    CharPLinearHostStatement := by
  intro K _ p hp hK n H hH
  obtain ⟨k, M, ψ, hψ⟩ := hcoord K p hp hK n H hH
  haveI : CharP K p := ringChar.of_eq hK
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right (by omega)⟩
  obtain ⟨f, hf⟩ := habs p (k + 1) M (k + 5 + 2 * M) (by omega) (by omega)
  have hE : Group.IsFinitelyPresented
      (elementaryGroup (Fin (k + 5 + 2 * M)) (CharPPoly p (k + 1))) :=
    hfp p (k + 1) (k + 5 + 2 * M) (by omega)
  haveI : Group.IsFinitelyPresented
      (AffineElementaryGroup (k + 5 + 2 * M) (CharPPoly p (k + 1))) :=
    haff (CharPPoly p (k + 1))
      (finiteType_int_transfer _
        (finiteType_int_of_surjective _ (charPPoly_map_surjective p (k + 1))) _)
      (k + 5 + 2 * M) (by omega) hE
  obtain ⟨X, _, _, ρ, hρ⟩ := hss p (k + 1) (k + 5 + 2 * M) (by omega) (by omega)
  exact embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ
    (f := f.comp ((glLift p k M).comp ψ)) (hf.comp ((glLift_injective p k M).comp hψ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.charPLinearHostStatement_of_chain

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
