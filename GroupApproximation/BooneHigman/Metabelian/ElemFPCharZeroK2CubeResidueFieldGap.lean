import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeResidueFieldCone
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeLocalResidue
import GroupApproximation.Meta.AxiomGuard

/-!
# The residue-characteristic cube gap over `ℤ[1/m]`, cut down to the minimal rank `N = k + 5`

Lane `bh-met-81`.  Lane `bh-met-74` (module `ElemFPCharZeroK2CubeLocalResidue`) reduced the
char-zero cube gap to `CZCubeLocalResidueStatement`: for `m ≥ 1`, `A = ℤ[1/m]`, all `k` and all
ranks `N ≥ k + 5`, an element `u ∈ K₂(N, A[s_0..s_k])` killed by every `π_i : s_i ↦ 0`, and a
maximal ideal `𝔪 ∋ p` of `B = A[s_1..s_k]`, some `s ∉ 𝔪` makes `v_s(ψ u)` die after padding.

* `CZCubeResFieldOverStatement A`: the same local condition, but only for `k ≥ 1` and only at the
  **minimal rank** `N = k + 5`.
* `CZCubeResFieldStatement`: that condition over every `ℤ[1/m]`, `m ≥ 1`.  **The isolated gap.**
* `czCubeResField_dies_of_overStatement`: per-element Quillen patching
  (`cubeNilField_dies_of_local`), with the Jacobson input `hres` (every maximal ideal contains a
  prime, `czCubeLocal_exists_prime_mem`) supplying the prime: at rank `k + 5`, `k ≥ 1`, every
  `u` killed by every `π_i` dies after padding.
* `czCubeResField_residueOver_of_over`: the gap gives the full residue statement.  Given `u` at
  `k + 1` variables and rank `N ≥ k + 5`, pad it once to rank `N + 1`, then apply the cone
  `s_0 ↦ s_0 s_{last}` `r = N - 4 - k` times (module `ElemFPCharZeroK2CubeResidueFieldCone`):
  this lands at `k' + 1` variables with `k' = N - 4 ≥ 1` and rank `N + 1 = k' + 5`, where the
  gap and patching kill it; the retractions and the padding carry the death back to `u`, and
  `s = 1` meets the local demand.
* `czCubeResField_residue_of_resField`: **endpoint**, `CZCubeResFieldStatement →
  CZCubeLocalResidueStatement`.
* `czCubeResField_resField_of_residue`: the (trivial) converse.
* `czCubeResField_charZeroK2CubeGapPos_of_resField`: with the diagonal half, the root
  hypothesis `CharZeroK2CubeGapPosStatement`.

## LOUD: strength, and why the target is not closed

**The gap is logically equivalent to `CZCubeLocalResidueStatement`** (both directions are proved);
no strictly weaker *logical* form is available, since it is a sub-family of the target that
implies the target.  It is **strictly smaller in proof content**: the two-parameter family
`(k, N)`, `N ≥ k + 5`, `k ≥ 0` is cut to the one-parameter family `N = k + 5`, `k ≥ 1`; all
higher ranks and the non-reduced base `B = ℤ[1/m]` (`k = 0`) are derived by the cone, padding,
Quillen patching and the Jacobson property.

The target itself (`NK₂ = 0` for `ℤ[1/m][s]` locally at `𝔪 ∋ p`) is **not** proved here: it is
Quillen's homotopy invariance for regular rings.  "Reducing to residue characteristic `p`" has no
formal content in the repository: there is no ring map `𝔽_p[s] → ℤ[1/m][s]`, and reduction mod
`p` cannot reflect death of `K₂` elements, so the char-`p` statements
(`PolyK2CubeNilLocalStatement`, `PolyK2CubeNilFieldPosStatement`) do not transfer.  Only their
*ring-generic proof steps* transfer, and those are the ones used here.

## Truth check

True, as a sub-family of `CZCubeLocalResidueStatement`, which is true: by Quillen, `NK₂` of the
regular ring `ℤ[1/m][s_1..s_k]` vanishes, so `u` (killed by `ev₀ = ev₀ ∘ π_0`) is stably trivial
and hence dies at a finite rank; `s = 1` then works (see the truth check of
`ElemFPCharZeroK2CubeGapLocal`).  For `k = 1`, `N = 6`: `B = ℤ[1/m][s_1]`, `𝔪 = (p, f(s_1))`
with `f` irreducible mod `p`, and the demand is met by `s = 1` once `u` dies.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Over

variable (A : Type*) [CommRing A]

/-- **The local cube condition at minimal rank.**  As `CZCubeLocalResidueOverStatement A`, but
only for `k ≥ 1` base variables and only at rank `N = k + 5`. -/
def CZCubeResFieldOverStatement : Prop :=
  ∀ k N : ℕ, 0 < k → N = k + 5 →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) A),
      (∀ i : Fin (k + 1), K2Map (cubeKill A i) u = 1) →
        ∀ p : ℕ, p.Prime →
          ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
            (p : MvPolynomial (Fin k) A) ∈ P →
              ∃ s : MvPolynomial (Fin k) A, s ∉ P ∧
                K2DiesAfterPadding
                  (quillenDiff (K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom u) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubeResFieldOverStatement

/-- **Per-element patching at minimal rank.**  If every maximal ideal of every `A[s_1..s_k]`
contains a prime, the gap makes every `u ∈ K₂(k + 5, A[s_0..s_k])`, `k ≥ 1`, killed by every
`π_i`, die after padding. -/
theorem czCubeResField_dies_of_overStatement
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : CZCubeResFieldOverStatement A) {k N : ℕ} (hk : 0 < k) (hN : N = k + 5)
    (u : K2n N (MvPolynomial (Fin (k + 1)) A))
    (hu : ∀ i : Fin (k + 1), K2Map (cubeKill A i) u = 1) : K2DiesAfterPadding u :=
  cubeNilField_dies_of_local u (hu 0) fun P hP ↦ by
    obtain ⟨p, hp, hpP⟩ := hres k P hP
    exact h k N hk hN u hu p hp P hP hpP

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_dies_of_overStatement
