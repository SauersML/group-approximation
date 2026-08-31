import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferSurjective
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Exact

/-!
# The Smith/Gysin connecting map in cohomology for `Sⁿ → RPⁿ`

This file constructs the genuine cohomology-level connecting homomorphism of the
double-cover Smith/Gysin sequence associated to the antipodal double cover
`Sⁿ → RPⁿ`, working over the field `F₂ = ZMod 2`.

The starting data (built in `RPnTopClassTransferSurjective.lean`) is the dualized
Smith short exact sequence of singular **cochain** complexes

```text
0 ⟶ C^•(RPⁿ; F₂) ──proj^*──▶ C^•(Sⁿ; F₂) ──tr──▶ C^•(RPⁿ; F₂) ⟶ 0
```

namely `transferSEScoch n` with `transferSEScoch_shortExact n`.  Writing
`S = transferSEScoch n`, its terms have homologies

```text
Hᵏ(S.X₁) = Hᵏ(RPⁿ),   Hᵏ(S.X₂) = Hᵏ(Sⁿ),   Hᵏ(S.X₃) = Hᵏ(RPⁿ)
```

(all definitional, see `transferSEScoch_X₁/₂/₃_homology`).  Mathlib's short-exact
API supplies the connecting map `S.ShortExact.δ i j hij : Hᵏ(S.X₃) ⟶ H^{k+1}(S.X₁)`
which here is a genuine morphism `Hᵏ(RPⁿ) ⟶ H^{k+1}(RPⁿ)`.  This is the
Smith/Gysin connecting map, packaged below as `rpGysinConnecting`.

## The relevant long-exact-sequence segment

The long exact cohomology sequence of `S` gives, around degree `k`,

```text
⋯ ──▶ Hᵏ(Sⁿ) ──tr──▶ Hᵏ(RPⁿ) ──δ──▶ H^{k+1}(RPⁿ) ──▶ ⋯
```

with `tr = cohTransferZMod2 n k` (the genuine cohomology transfer, i.e. the
homology map of `S.g`) and `δ = rpGysinConnecting n k`.  Exactness of this
segment at the middle term `Hᵏ(RPⁿ)` is Mathlib's `homology_exact₃`, recorded
here as `rpGysin_exact_at_middle`; the corresponding submodule identity
`ker δ = range tr` is `rpGysin_kernel_eq_image`.  Concretely (the form needed for
the later Gysin induction):

```text
if x ∈ Hᵏ(RPⁿ) and δ x = 0, then x lies in the image of the transfer Hᵏ(Sⁿ) ⟶ Hᵏ(RPⁿ).
```
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The Smith/Gysin cohomology connecting map** for the double cover
`Sⁿ → RPⁿ` over `F₂`.  It is the connecting homomorphism of the dualized Smith
short exact sequence `transferSEScoch n`, a genuine morphism
`Hᵏ(RPⁿ; F₂) ⟶ H^{k+1}(RPⁿ; F₂)`.

The source `(transferSEScoch n).X₃.homology k` and target
`(transferSEScoch n).X₁.homology (k+1)` are definitionally `rpCohomology n k`
and `rpCohomology n (k+1)` (see `transferSEScoch_X₃_homology`,
`transferSEScoch_X₁_homology`). -/
noncomputable def rpGysinConnecting (n k : ℕ) :
    rpCohomology n k ⟶ rpCohomology n (k + 1) :=
  (transferSEScoch_shortExact n).δ k (k + 1) rfl

/-- The Smith/Gysin connecting map is, definitionally, Mathlib's short-exact
connecting homomorphism `δ` of `transferSEScoch n`. -/
theorem rpGysinConnecting_eq_δ (n k : ℕ) :
    rpGysinConnecting n k = (transferSEScoch_shortExact n).δ k (k + 1) rfl :=
  rfl

/-- **Exactness at the middle term of the Gysin segment.**  The segment

```text
Hᵏ(Sⁿ) ──tr──▶ Hᵏ(RPⁿ) ──δ──▶ H^{k+1}(RPⁿ)
```

of the long exact cohomology sequence is exact at `Hᵏ(RPⁿ)`, where
`tr = cohTransferZMod2 n k` and `δ = rpGysinConnecting n k`.  This is stated in
`Function.Exact` form: the range of the transfer equals the kernel of the
connecting map. -/
theorem rpGysin_exact_at_middle (n k : ℕ) :
    Function.Exact (cohTransferZMod2 n k).hom (rpGysinConnecting n k).hom := by
  have hSE := transferSEScoch_shortExact n
  have hex := hSE.homology_exact₃ k (k + 1) rfl
  have hker := hex.moduleCat_range_eq_ker
  rw [LinearMap.exact_iff]
  rw [← transferSEScoch_homologyMap_g n k]
  exact hker.symm

/-- **Kernel = image for the Gysin segment.**  As submodules of `Hᵏ(RPⁿ; F₂)`,
the kernel of the connecting map `rpGysinConnecting n k` equals the image of the
cohomology transfer `cohTransferZMod2 n k : Hᵏ(Sⁿ) ⟶ Hᵏ(RPⁿ)`. -/
theorem rpGysin_kernel_eq_image (n k : ℕ) :
    LinearMap.ker (rpGysinConnecting n k).hom
      = LinearMap.range (cohTransferZMod2 n k).hom := by
  have hSE := transferSEScoch_shortExact n
  have hex := hSE.homology_exact₃ k (k + 1) rfl
  have hker := hex.moduleCat_range_eq_ker
  rw [← transferSEScoch_homologyMap_g n k]
  exact hker.symm

/-- **The form needed for the Gysin induction.**  If `x ∈ Hᵏ(RPⁿ; F₂)` is killed
by the Smith/Gysin connecting map, then `x` lies in the image of the cohomology
transfer `Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂)`. -/
theorem rpGysin_mem_image_of_connecting_eq_zero (n k : ℕ) (x : rpCohomology n k)
    (hx : (rpGysinConnecting n k).hom x = 0) :
    x ∈ LinearMap.range (cohTransferZMod2 n k).hom := by
  rw [← rpGysin_kernel_eq_image]
  exact hx

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

