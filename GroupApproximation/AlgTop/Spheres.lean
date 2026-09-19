import GroupApproximation.AlgTop.UniversalCoefficients
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV

/-!
# The integral cohomology generator of `Sⁿ` and the top-degree pairing

The vendored development already proves, unconditionally, that
`Hₙ(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1` — this is
`sphereTopHomologyIso_unconditional`, assembled from the Mayer–Vietoris
suspension tower. Feeding that identification through the surjectivity half of
the universal coefficient theorem produces a **cohomology** class pairing to `1`
against the homology generator, which is what a top-degree pairing is.

## Main definitions

* `Sph n` — the `n`-sphere as an object of `TopCat`.
* `sphereFundamentalClass n hn : Hₙ(Sⁿ; ℤ)` — the generator `[Sⁿ]`.
* `sphereGen n hn : Hⁿ(Sⁿ; ℤ)` — the dual generator.
* `spherePairing n hn : Hⁿ(Sⁿ; ℤ) →ₗ[ℤ] ℤ` — `⟨·, [Sⁿ]⟩`.

## Main results

* `spherePairing_sphereGen` — the pairing is normalised: `⟨gen, [Sⁿ]⟩ = 1`.
* `sphereGen_ne_zero`.

## What is deliberately not here

The statement `Hⁿ(Sⁿ; ℤ) ≅ ℤ` needs the *injectivity* half of the universal
coefficient theorem at degree `n`, hence `Hₙ₋₁(Sⁿ; ℤ)` projective. For `n = 1`
that is `H₀(S¹; ℤ) ≅ ℤ`; for `n ≥ 2` it is `0`, but the vendored tree does not
package integral off-degree vanishing (it has the contractible, disk, point and
mod-2 cases only). Everything the Euler-class and obstruction lanes need is the
*pairing*, which needs only surjectivity and is proved here.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

noncomputable section

/-- The `n`-sphere as an object of `TopCat`, in the vendored `Metric.sphere`
model. Design constraint C2: this is the one sphere model the cohomology is
computed in, and `SphereModelTransport` is the one transport to any other. -/
abbrev Sph (n : ℕ) : TopCat.{0} := TopCat.of (Sphere n)

/-- **`Hₙ(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1`**, transported from the vendored
Mayer–Vietoris suspension tower to the raw sphere model. -/
def sphereHomologyIso (n : ℕ) (hn : 1 ≤ n) :
    homologyOf ℤ (Sph n) n ≅ ModuleCat.of ℤ ℤ :=
  modelIso_of_sphereTopHomologyIso (sphereTopHomologyIso_unconditional n hn)

/-- The **fundamental class** `[Sⁿ] ∈ Hₙ(Sⁿ; ℤ)`: the preimage of `1`. -/
def sphereFundamentalClass (n : ℕ) (hn : 1 ≤ n) : homologyOf ℤ (Sph n) n :=
  (sphereHomologyIso n hn).inv.hom (1 : ℤ)

/-- The functional on `Hₙ(Sⁿ; ℤ)` reading off the coefficient with respect to the
fundamental class. -/
def sphereFunctional (n : ℕ) (hn : 1 ≤ n) : homologyOf ℤ (Sph n) n →ₗ[ℤ] ℤ :=
  (sphereHomologyIso n hn).hom.hom

theorem sphereFunctional_fundamentalClass (n : ℕ) (hn : 1 ≤ n) :
    sphereFunctional n hn (sphereFundamentalClass n hn) = 1 := by
  show (sphereHomologyIso n hn).hom.hom ((sphereHomologyIso n hn).inv.hom (1 : ℤ)) = 1
  rw [← ModuleCat.comp_apply, (sphereHomologyIso n hn).inv_hom_id]
  rfl

/-- The **chosen generator** of `Hⁿ(Sⁿ; ℤ)`: a class whose Kronecker image is the
coefficient functional. It exists by surjectivity of the Kronecker map, which is
where the arbitrary-rank freeness of submodules over a PID is used. -/
def sphereGen (n : ℕ) (hn : 1 ≤ n) : cohomologyℤ (Sph n) n :=
  (kronecker_surjective ℤ (Sph n) n (sphereFunctional n hn)).choose

theorem kronecker_sphereGen (n : ℕ) (hn : 1 ≤ n) :
    (kronecker ℤ (Sph n) n).hom (sphereGen n hn) = sphereFunctional n hn :=
  (kronecker_surjective ℤ (Sph n) n (sphereFunctional n hn)).choose_spec

/-- **The top-degree pairing** `⟨·, [Sⁿ]⟩ : Hⁿ(Sⁿ; ℤ) →ₗ[ℤ] ℤ`. -/
def spherePairing (n : ℕ) (hn : 1 ≤ n) : cohomologyℤ (Sph n) n →ₗ[ℤ] ℤ where
  toFun a := (kronecker ℤ (Sph n) n).hom a (sphereFundamentalClass n hn)
  map_add' a b := by
    show ((kronecker ℤ (Sph n) n).hom (a + b)) (sphereFundamentalClass n hn)
      = ((kronecker ℤ (Sph n) n).hom a) (sphereFundamentalClass n hn)
        + ((kronecker ℤ (Sph n) n).hom b) (sphereFundamentalClass n hn)
    rw [map_add]
    rfl
  map_smul' s a := by
    show ((kronecker ℤ (Sph n) n).hom (s • a)) (sphereFundamentalClass n hn)
      = s • ((kronecker ℤ (Sph n) n).hom a) (sphereFundamentalClass n hn)
    rw [map_smul]
    rfl

@[simp] theorem spherePairing_apply (n : ℕ) (hn : 1 ≤ n) (a : cohomologyℤ (Sph n) n) :
    spherePairing n hn a = (kronecker ℤ (Sph n) n).hom a (sphereFundamentalClass n hn) := rfl

/-- **The pairing is normalised**: the chosen generator pairs to `1`. -/
@[simp] theorem spherePairing_sphereGen (n : ℕ) (hn : 1 ≤ n) :
    spherePairing n hn (sphereGen n hn) = 1 := by
  rw [spherePairing_apply, kronecker_sphereGen, sphereFunctional_fundamentalClass]

theorem sphereGen_ne_zero (n : ℕ) (hn : 1 ≤ n) : sphereGen n hn ≠ 0 := by
  intro h
  have h1 := spherePairing_sphereGen n hn
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The pairing is surjective onto `ℤ`: every integer is realised. -/
theorem spherePairing_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (spherePairing n hn) := by
  intro k
  refine ⟨k • sphereGen n hn, ?_⟩
  rw [map_smul, spherePairing_sphereGen, smul_eq_mul, mul_one]

end

end GroupApproximation.AlgTop
