import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 6: the local Quillen Statement up to elementary operations

Lane `bh-met-60`.  Target: `SuslinLocalGlobalQuillenStatement` (`SuslinLocalGlobalPatching.lean`).

**Truth check of the target.**  TRUE, by Suslin's theorem (A. A. Suslin, 1977):
for `A = F_p[s_0, ..., s_{k-1}]` or `A = ℤ[1/m][t_0, ..., t_{k-1}]` and `N ≥ 3`,
`SL_N(A[X]) = E_N(A[X])`, so every normalized `τ` is elementary and `a = 1 ∉ 𝔪` lies in
`Q(τ)`.  It is NOT closed here.

**Isolated Statement.**  `SuslinLocalHorrocksStatement` has the same hypotheses and, for a
normalized `τ ∈ SL_N(A[X])` and a maximal ideal `𝔪`, only asks for SOME `ε ∈ E_N(A[X])`, SOME
constant `g ∈ GL_N(A)` and SOME `a ∉ 𝔪` with `a ∈ Q(ε τ C(g))`.

* It is strictly weaker in logical strength: `ε = 1`, `g = 1` recovers the target's condition.
* It is true: by Suslin's theorem as above, take `ε = 1`, `g = 1`, `a = 1`.
* The reduction `suslinLocalGlobalQuillen_of_localHorrocks` is proved from
  `Q(ε τ C(g)) = Q(τ)` (`SuslinLocalHorrocksInvariance.lean`; no normality of `E_N` used).

**Loud caveat.**  The proof content removed is only the bookkeeping of elementary row operations
and constant corrections.  The mathematical core of the gap is unchanged and still open:

1. local Horrocks: `τ_𝔪 ∈ E_N(A_𝔪[X])` over the local ring `A_𝔪`;
2. clearing denominators: some `s ∉ 𝔪` with `τ_s ∈ E_N(A_s[X])`;
3. Suslin's dilation principle for `σ = τ(X + Y) τ(X)⁻¹` (needs normality of `E_N`, `N ≥ 3`,
   sibling lane `bh-met-39b`; no `SuslinNormal*` interface exists in the repository yet),
   giving `s^k ∈ Q(τ)`.

None of 1–3 is formalized in this lane (no localization machinery for `E_N` exists in the
corpus; the dilation principle alone is a long commutator-calculus argument).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Every normalized `τ ∈ SL_N(A[X])` has, for each maximal ideal `𝔪`, some elementary
`ε ∈ E_N(A[X])`, constant `g ∈ GL_N(A)` and `a ∉ 𝔪` with `a ∈ Q(ε τ C(g))`. -/
def SuslinLocalHorrocksLocallyQuillen (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
          ∃ ε ∈ elementaryGroup (Fin N) (Polynomial A),
            ∃ g : Matrix.GeneralLinearGroup (Fin N) A, ∃ a ∉ 𝔪,
              SuslinLocalGlobalQuillen
                (ε * τ * elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) g) a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalHorrocksLocallyQuillen

/-- Quillen elements up to elementary operations are Quillen elements. -/
theorem suslinLocallyQuillen_of_localHorrocks {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinLocalHorrocksLocallyQuillen A N) : SuslinLocalGlobalLocallyQuillen A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨ε, hε, g, a, ha𝔪, ha⟩ := h τ hdet h0 𝔪 h𝔪
  exact ⟨a, ha𝔪, suslinLocalHorrocks_quillen_of_elementary_mul_C hε g ha⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocallyQuillen_of_localHorrocks

/-- **The local Horrocks Statement**: `SuslinLocalHorrocksLocallyQuillen` for the two
coefficient families, under the hypotheses of `SuslinLocalGlobalQuillenStatement`. -/
def SuslinLocalHorrocksStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinLocalHorrocksLocallyQuillen (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinLocalHorrocksLocallyQuillen (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalHorrocksStatement

/-- **The reduction**: the local Horrocks Statement gives the local Quillen Statement. -/
theorem suslinLocalGlobalQuillen_of_localHorrocks (h : SuslinLocalHorrocksStatement) :
    SuslinLocalGlobalQuillenStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinLocallyQuillen_of_localHorrocks (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinLocallyQuillen_of_localHorrocks (h.2 m k N hA hN)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalQuillen_of_localHorrocks

/-- The patching Statement from the local Horrocks Statement. -/
theorem suslinPatching_of_localHorrocks (h : SuslinLocalHorrocksStatement) :
    SuslinPatchingStatement :=
  suslinPatching_of_localGlobalQuillen (suslinLocalGlobalQuillen_of_localHorrocks h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinPatching_of_localHorrocks

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
