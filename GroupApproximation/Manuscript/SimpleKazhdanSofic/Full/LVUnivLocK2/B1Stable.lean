import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Steinberg-level interface for `K₂`-localization sequences (lane LVUnivLocK2-B1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, input W1
(stable `K₂(L_{𝔽₂}(1,2)) = 0`).  Work order WO-LVK2Route-2 (Core-B) and WO-LVK2Route-1 (Core-A)
both reduce W1 to the **base surjectivity** `LVStableK2.StableK2BaseSurjective f` of a
localization map `f : R → S`.  Quillen's localization theorem (Quillen 1973 §5 Thm 5; Grayson;
Neeman–Ranicki 2004) gives exactness of `K₂(R) → K₂(S) → K₁(T)` with `T` the torsion category.

This file fixes the Steinberg-level form of that sequence, so that the localization lane (B2),
the dévissage lane (B4) and the Ore lane (LVOreLocK2) share one target statement:

* `K2ExactAt f A`: a boundary `K₂(n, S) → A` (all `n`) whose kernel consists of stable images of
  `K₂(R)`; this is exactness of `K₂(R) → K₂(S) → A` at `K₂(S)`, in finite-stage form;
* `K2ExactAt.baseSurjective`: if `A` is trivial (e.g. `A = K₁(T) = 0` by dévissage), `f` is
  base surjective;
* `RelKOneInjective f`: the relative form.  With the Steinberg model of the relative group
  `K₁(f) = {(a, σ) ∈ E(R) × St(S) : f(a) = φ(σ)} / St(R)` it says `K₁(f) → K₁(R)` is injective;
  `stableK2BaseSurjective_iff_relKOneInjective` proves it is equivalent to base surjectivity
  (the elementary part of the long exact sequence `K₂(R) → K₂(S) → K₁(f) → K₁(R)`);
* `stableK2BaseSurjective_comp`, `stableK2BaseSurjective_of_comp`: base surjectivity composes,
  and descends along the second factor.

Nothing here uses the Q-construction; the comparison of these Steinberg-level groups with
Quillen's `K₂` of the exact category of finitely generated projective modules is the separate
work order recorded in the lane status (`LVUnivLocK2-B1`).
-/

namespace GroupApproximation.Full.LVUnivLocK2

open SteinbergGroup

section Exactness

variable {R S : Type*} [Ring R] [Ring S]

/-- **Exactness of `K₂(R) → K₂(S) → A` at `K₂(S)`, finite-stage form.**  A boundary map defined
on every `K₂(n, S) = ker (St_n(S) → E_n(S))`, such that every element with trivial boundary
becomes, after padding, the image of an element of some `K₂(N, R)`.  For a localization
`f : R → Σ⁻¹R` the boundary is Quillen's `∂ : K₂(Σ⁻¹R) → K₁(T_Σ)` (Quillen 1973 §5 Thm 5;
Neeman–Ranicki 2004).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
structure K2ExactAt (f : R →+* S) (A : Type*) [Group A] where
  /-- The boundary map on `K₂(n, S)`. -/
  boundary : ∀ (n : ℕ) (k : SteinbergGroup (Fin n) S), projection k = 1 → A
  /-- Exactness: elements with trivial boundary lift stably to `K₂(R)`. -/
  lift_of_boundary : ∀ (n : ℕ) (k : SteinbergGroup (Fin n) S) (hk : projection k = 1),
    boundary n k hk = 1 →
      ∃ (N : ℕ) (h : n ≤ N) (y : SteinbergGroup (Fin N) R),
        projection y = 1 ∧ ringMap f y = indexMap (Fin.castLEEmb h) k

namespace K2ExactAt

variable {f : R →+* S} {A : Type*} [Group A]

/-- If every boundary is trivial, `f` is base surjective on stable `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem baseSurjective_of_boundary_eq_one (E : K2ExactAt f A)
    (h : ∀ (n : ℕ) (k : SteinbergGroup (Fin n) S) (hk : projection k = 1),
      E.boundary n k hk = 1) :
    LVStableK2.StableK2BaseSurjective f := by
  intro n k hk
  exact E.lift_of_boundary n k hk (h n k hk)

/-- **Vanishing target gives base surjectivity.**  If the target `A` of the boundary is trivial
(for a localization: `K₁(T_Σ) = 0`, by dévissage), then `K₂(R) → K₂(S)` is stably onto.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem baseSurjective [Subsingleton A] (E : K2ExactAt f A) :
    LVStableK2.StableK2BaseSurjective f :=
  E.baseSurjective_of_boundary_eq_one fun _ _ _ => Subsingleton.elim _ _

end K2ExactAt

/-- Base surjectivity is exactness with trivial target: the canonical `K2ExactAt f Unit`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def k2ExactAtUnit (f : R →+* S) (hB : LVStableK2.StableK2BaseSurjective f) :
    K2ExactAt f Unit where
  boundary _ _ _ := 1
  lift_of_boundary n k hk _ := hB n k hk

end Exactness

section Relative

variable {R S : Type*} [Ring R] [Ring S]

/-- **Injectivity of relative `K₁(f) → K₁(R)`, finite-stage form.**  Model the relative group of
`f : R → S` by pairs `(a, σ)` with `a ∈ E_n(R)`, `σ ∈ St_n(S)` and `f(a) = φ(σ)`, modulo the
image `τ ↦ (φ(τ), f(τ))` of `St(R)`.  Writing `a = φ(τ₀)`, the class of `(a, σ)` maps to
`[a] = 0 ∈ K₁(R)`; injectivity asks that `(a, σ)` is stably the image of some `τ ∈ St_N(R)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def RelKOneInjective (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (τ₀ : SteinbergGroup (Fin n) R) (σ : SteinbergGroup (Fin n) S),
    projection (ringMap f τ₀) = projection σ →
      ∃ (N : ℕ) (h : n ≤ N) (τ : SteinbergGroup (Fin N) R),
        projection τ = projection (indexMap (Fin.castLEEmb h) τ₀) ∧
          ringMap f τ = indexMap (Fin.castLEEmb h) σ

/-- Base surjectivity gives relative injectivity: correct `τ₀` by a stable lift of the
`K₂(S)`-element `f(τ₀)⁻¹ σ`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem relKOneInjective_of_baseSurjective (f : R →+* S)
    (hB : LVStableK2.StableK2BaseSurjective f) : RelKOneInjective f := by
  intro n τ₀ σ hτσ
  have hk : projection ((ringMap f τ₀)⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, hτσ, inv_mul_cancel]
  obtain ⟨N, hN, y, hy1, hy⟩ := hB n ((ringMap f τ₀)⁻¹ * σ) hk
  refine ⟨N, hN, indexMap (Fin.castLEEmb hN) τ₀ * y, ?_, ?_⟩
  · rw [map_mul, hy1, mul_one]
  · calc ringMap f (indexMap (Fin.castLEEmb hN) τ₀ * y)
        = ringMap f (indexMap (Fin.castLEEmb hN) τ₀) * ringMap f y :=
          map_mul (ringMap f) _ _
      _ = indexMap (Fin.castLEEmb hN) (ringMap f τ₀) *
            indexMap (Fin.castLEEmb hN) ((ringMap f τ₀)⁻¹ * σ) := by
          rw [hy, LVStableK2.indexMap_ringMap]
      _ = indexMap (Fin.castLEEmb hN) (ringMap f τ₀ * ((ringMap f τ₀)⁻¹ * σ)) :=
          (map_mul (indexMap (Fin.castLEEmb hN)) _ _).symm
      _ = indexMap (Fin.castLEEmb hN) σ := by rw [mul_inv_cancel_left]

/-- Relative injectivity gives base surjectivity (take `τ₀ = 1`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem baseSurjective_of_relKOneInjective (f : R →+* S) (hR : RelKOneInjective f) :
    LVStableK2.StableK2BaseSurjective f := by
  intro n k hk
  have h1 : projection (ringMap f (1 : SteinbergGroup (Fin n) R)) = projection k := by
    rw [map_one, map_one, hk]
  obtain ⟨N, hN, τ, hτ1, hτ⟩ := hR n 1 k h1
  refine ⟨N, hN, τ, ?_, hτ⟩
  rw [hτ1, map_one, map_one]

/-- **Base surjectivity is injectivity of relative `K₁(f) → K₁(R)`** (the elementary part of
the exact sequence `K₂(R) → K₂(S) → K₁(f) → K₁(R)`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2BaseSurjective_iff_relKOneInjective (f : R →+* S) :
    LVStableK2.StableK2BaseSurjective f ↔ RelKOneInjective f :=
  ⟨relKOneInjective_of_baseSurjective f, baseSurjective_of_relKOneInjective f⟩

end Relative

section Composition

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- **Base surjectivity composes.**  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2BaseSurjective_comp (f : R →+* S) (g : S →+* T)
    (hf : LVStableK2.StableK2BaseSurjective f) (hg : LVStableK2.StableK2BaseSurjective g) :
    LVStableK2.StableK2BaseSurjective (g.comp f) := by
  intro n k hk
  obtain ⟨N₁, h₁, y₁, hy₁, hgy₁⟩ := hg n k hk
  obtain ⟨N₂, h₂, y₂, hy₂, hfy₂⟩ := hf N₁ y₁ hy₁
  refine ⟨N₂, h₁.trans h₂, y₂, hy₂, ?_⟩
  rw [← LVCohnK2.ringMap_ringMap, hfy₂, ← LVStableK2.indexMap_ringMap, hgy₁,
    LVH2GL3.indexMap_castLEEmb_castLEEmb]

/-- **Base surjectivity descends along the second factor**: if `K₂(R) → K₂(T)` is stably onto
through `S`, so is `K₂(S) → K₂(T)`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2BaseSurjective_of_comp (f : R →+* S) (g : S →+* T)
    (h : LVStableK2.StableK2BaseSurjective (g.comp f)) :
    LVStableK2.StableK2BaseSurjective g := by
  intro n k hk
  obtain ⟨N, hN, y, hy1, hy⟩ := h n k hk
  refine ⟨N, hN, ringMap f y, ?_, ?_⟩
  · rw [LVCohnK2.projection_ringMap, hy1, map_one]
  · rw [LVCohnK2.ringMap_ringMap, hy]

end Composition

end GroupApproximation.Full.LVUnivLocK2
