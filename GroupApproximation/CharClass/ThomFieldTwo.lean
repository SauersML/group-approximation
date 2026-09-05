import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

/-!
# One-dimensional `F₂`-modules: surjections are isomorphisms

The very last step of Step C of the LIX obstruction (see
`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3) is the following triviality, which
is nevertheless worth isolating because it is where the whole odd-side argument
is discharged:

> the restriction `j^* : H^{2r}(N, N ∖ z; F₂) → H^{2r}(N; F₂)` is a *surjection*
> (the long exact sequence of the pair, plus `H^{2r}(N ∖ z; F₂) = 0`), and both
> sides are one dimensional over `F₂`; so `j^*` is injective, and the relative
> Euler class `s^* u ≠ 0` has `γ_r(W) = j^*(s^* u) ≠ 0`.

Nothing here mentions topology.  The base ring is any *finite* ring `R` (the use
is `R = ZMod 2`); "one dimensional" is spelled as a linear equivalence with `R`,
because that is the form in which the Künneth and excision computations of the
peer lanes deliver it.

## Main results

* `injective_of_surjective_of_linearEquiv` — a surjective `R`-linear map between
  two modules each linearly equivalent to `R` (with `R` finite) is injective.
* `ne_zero_of_surjective_of_linearEquiv` — the same, in the form actually used:
  a nonzero class stays nonzero.
* `surjective_of_exact_of_subsingleton` — exactness at the middle term of
  `M → N → P` with `P` a subsingleton makes `M → N` surjective; this is how the
  long exact sequence of the pair delivers the surjectivity hypothesis once
  `H^{2r}(N ∖ z)` is known to vanish.
* `ModuleCat` restatements (`ModuleCat.ne_zero_of_surjective_of_linearEquiv`,
  `ModuleCat.hom_surjective_of_exact_of_subsingleton`), because the vendored
  singular cohomology takes values in `ModuleCat.{0} (ZMod 2)`.
-/

namespace GroupApproximation.CharClass

open Function

section Finite

variable {R : Type*} [Ring R] [Finite R]
variable {M N P : Type*}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- **A surjection between one-dimensional modules is injective.**  If `M` and `N` are
both linearly equivalent to the finite base ring `R`, then any surjective `R`-linear
map `M → N` is injective: after transporting along the two equivalences it becomes a
surjective self-map of the finite type `R`. -/
theorem injective_of_surjective_of_linearEquiv (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R)
    {f : M →ₗ[R] N} (hf : Surjective f) : Injective f := by
  have : Finite M := Finite.of_equiv R eM.symm.toEquiv
  exact (Finite.injective_iff_surjective_of_equiv
    (eM.toEquiv.trans eN.symm.toEquiv)).2 hf

/-- **A surjection between one-dimensional modules does not kill anything.**  This is
the form in which Step C uses `injective_of_surjective_of_linearEquiv`: the relative
Euler class `s^* u` is a nonzero element of `H^{2r}(N, N ∖ z)`, and its restriction
`γ_r = j^*(s^* u)` is therefore nonzero. -/
theorem ne_zero_of_surjective_of_linearEquiv (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R)
    {f : M →ₗ[R] N} (hf : Surjective f) {x : M} (hx : x ≠ 0) : f x ≠ 0 := by
  intro hfx
  refine hx (injective_of_surjective_of_linearEquiv eM eN hf ?_)
  rw [hfx, map_zero]

omit [Finite R] in
/-- **Exactness plus a vanishing cokernel term gives surjectivity.**  If
`M →f→ N →g→ P` is exact at `N` (`range f = ker g`) and `P` is a subsingleton, then
`f` is surjective.  Applied to the long exact sequence of the pair `(N, N ∖ z)` with
`P = H^{2r}(N ∖ z; F₂) = 0`, this is the surjectivity of `j^*`. -/
theorem surjective_of_exact_of_subsingleton [Subsingleton P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hexact : LinearMap.range f = LinearMap.ker g) :
    Surjective f := by
  intro y
  have hy : y ∈ LinearMap.ker g := by
    simp [LinearMap.mem_ker, Subsingleton.elim (g y) 0]
  rw [← hexact] at hy
  exact LinearMap.mem_range.1 hy

end Finite

namespace ModuleCat

variable {R : Type*} [Ring R] [Finite R]

/-- `ModuleCat` restatement of `ne_zero_of_surjective_of_linearEquiv`, in the shape in
which the vendored singular cohomology `cohomologyZMod2 X n : ModuleCat.{0} (ZMod 2)`
presents it. -/
theorem ne_zero_of_surjective_of_linearEquiv {M N : ModuleCat.{0} R}
    (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R) {f : M ⟶ N} (hf : Surjective f.hom)
    {x : M} (hx : x ≠ 0) : f.hom x ≠ 0 :=
  CharClass.ne_zero_of_surjective_of_linearEquiv eM eN hf hx

/-- `ModuleCat` restatement of `surjective_of_exact_of_subsingleton`. -/
theorem hom_surjective_of_exact_of_subsingleton {M N P : ModuleCat.{0} R}
    [Subsingleton P] (f : M ⟶ N) (g : N ⟶ P)
    (hexact : LinearMap.range f.hom = LinearMap.ker g.hom) : Surjective f.hom :=
  CharClass.surjective_of_exact_of_subsingleton f.hom g.hom hexact

end ModuleCat

end GroupApproximation.CharClass
