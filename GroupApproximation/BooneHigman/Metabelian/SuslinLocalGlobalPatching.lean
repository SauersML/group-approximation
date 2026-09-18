import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalQuillen
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 4: the patching Statement from local Quillen elements

Lane `bh-met-53`.  Target: `SuslinPatchingStatement` (`SuslinMonicPatching.lean`).

**Truth check.**  The target is TRUE: for `A = F_p[s_0, ..., s_{k-1}]` and
`A = ℤ[1/m][t_0, ..., t_{k-1}]`, Suslin's theorem (A. A. Suslin, *On the structure of the
special linear group over polynomial rings*, 1977) gives `SL_N(A[X]) = E_N(A[X])` for `N ≥ 3`,
so in particular every normalized `τ` is elementary.  It is not closed in this lane.

**Isolated Statement.**  `SuslinLocalGlobalQuillenStatement` has the same hypotheses as
`SuslinPatchingStatement` and asks, for a normalized `τ ∈ SL_N(A[X])` and every maximal ideal
`𝔪`, for ONE element `a ∉ 𝔪` of the Quillen set
`Q(τ) = {a : τ(X + aY) τ(X)⁻¹ ∈ E_N(A[X][Y])}`.

* It is true: by Suslin's theorem `τ ∈ E_N(A[X])`, hence its image `τ(X + Y)` is elementary
  over `A[X][Y]`, and so is `τ(X)⁻¹`; thus `a = 1 ∉ 𝔪` works.
* It is strictly smaller in proof content: the whole global half of the local-global
  principle is proved (`suslinLocalGlobal_mem_elementaryGroup`, `SuslinLocalGlobalQuillen.lean`):
  `Q(τ)` is an ideal, so it is `A` once it meets the complement of every maximal ideal, and
  `a = 1` together with the substitution `X ↦ 0, Y ↦ X` gives `τ ∈ E_N(A[X])`.
  No rank bound, determinant condition or normality of `E_N` is used there.

**Remaining gap** (purely local, one maximal ideal at a time):

1. local Horrocks: `τ_𝔪 ∈ E_N(A_𝔪[X])`, by Euclidean reduction on a monic entry;
2. clearing denominators: some `s ∉ 𝔪` with `τ_s ∈ E_N(A_s[X])`;
3. Suslin's dilation lemma (needs the normality of `E_N` for `N ≥ 3`, sibling lane `bh-met-39`):
   `σ = τ(X + Y) τ(X)⁻¹` has `σ(Y = 0) = 1` and `σ_s` elementary, hence
   `σ(X, s^k Y) ∈ E_N(A[X][Y])` for some `k`, i.e. `s^k ∈ Q(τ)`, and `s^k ∉ 𝔪`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Every normalized `τ ∈ SL_N(A[X])` has, for each maximal ideal `𝔪`, an element `a ∉ 𝔪` with
`τ(X + aY) τ(X)⁻¹ ∈ E_N(A[X][Y])`. -/
def SuslinLocalGlobalLocallyQuillen (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ a ∉ 𝔪, SuslinLocalGlobalQuillen τ a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalGlobalLocallyQuillen

/-- Quillen patching turns local Quillen elements into the normalized elementary conclusion. -/
theorem suslinNormalized_of_locallyQuillen {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinLocalGlobalLocallyQuillen A N) : SuslinMonicNormalizedElementary A N := by
  intro τ hdet h0
  exact suslinLocalGlobal_mem_elementaryGroup τ h0 (h τ hdet h0)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormalized_of_locallyQuillen

/-- **The local Quillen Statement**: `SuslinLocalGlobalLocallyQuillen` for the two coefficient
families, under the hypotheses of `SuslinPatchingStatement`. -/
def SuslinLocalGlobalQuillenStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinLocalGlobalLocallyQuillen (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinLocalGlobalLocallyQuillen (Chain.SIntPoly m k) N

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalGlobalQuillenStatement

/-- **The reduction**: local Quillen elements give the patching Statement. -/
theorem suslinPatching_of_localGlobalQuillen (h : SuslinLocalGlobalQuillenStatement) :
    SuslinPatchingStatement :=
  ⟨fun p _ k N hk hA hN ↦
      suslinNormalized_of_locallyQuillen (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinNormalized_of_locallyQuillen (h.2 m k N hA hN)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinPatching_of_localGlobalQuillen

/-- The one-variable Suslin step from local Quillen elements. -/
theorem suslinOneVariable_of_localGlobalQuillen (h : SuslinLocalGlobalQuillenStatement) :
    SuslinOneVariableStatement :=
  suslinOneVariable_of_patching (suslinPatching_of_localGlobalQuillen h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinOneVariable_of_localGlobalQuillen

/-- Both chain absorption leaves from local Quillen elements. -/
theorem elementaryAbsorption_of_localGlobalQuillen
    (h : SuslinLocalGlobalQuillenStatement) :
    Chain.CharPElementaryAbsorptionStatement ∧ Chain.CharZeroElementaryAbsorptionStatement :=
  elementaryAbsorptionStatements_of_patching (suslinPatching_of_localGlobalQuillen h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.elementaryAbsorption_of_localGlobalQuillen

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
