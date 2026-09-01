import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualTopPowerFinalAssembly
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNoCup
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferSurjective
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNaturality
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyDimensionVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereTopCohomologyRankOne
import GroupApproximation.Meta.AxiomGuard
import Mathlib

/-!
# Prompt 06 — Assemble `OddMapFixesTopClass n` from the isolated top-dimension gap

This file removes the `RPnCellularCochainStructure n` input from the top-class
transfer and, through it, from `OddMapFixesTopClass n`.  It isolates the *single*
genuinely-missing topological fact that the whole RPⁿ-cohomology side of the
project still depends on:

```text
IsZero (rpCohomology n (n+1))    -- i.e. Hⁿ⁺¹(RPⁿ; F₂) = 0
```

(vanishing of mod-2 cohomology exactly one degree above the dimension of `RPⁿ`).

## The reduction

* `cohTransferZMod2_top_surjective_of_vanish` — top-degree surjectivity of the
  genuine cohomology transfer follows from the dualized Smith short exact
  sequence together with `Hⁿ⁺¹(RPⁿ; F₂) = 0` alone (no cellular datum).
* `rpCohomology_top_finrank_one_of_vanish` — `dim Hⁿ(RPⁿ; F₂) = 1`, deduced from
  that surjectivity, the unconditional top sphere rank one
  (`sphere_top_cohomology_finrank_one`), and the unconditional nonvanishing
  `actualRPAlpha_topPower_ne_zero_no_cup` of `αⁿ`.
* `cohTransferZMod2_top_injective_of_vanish` — the surjection between two equal
  one-dimensional `F₂`-spaces is injective.
* `construct_RPnTopClassTransfer_of_topVanish` — the project's double-cover
  transfer predicate `RPnTopClassTransfer n`, built directly from the resulting
  linear isomorphism and the transfer naturality square, with **no**
  `RPnCellularCochainStructure n` and **no** `TopHomologyTransferNonzeroWitness n`.
* `oddMapFixesTopClass_of_topVanish` — the payoff, `OddMapFixesTopClass n`, from
  `hn` and the single vanishing fact.

The direct projective-space dimension computation supplies this vanishing
unconditionally, so the final theorem in this file has no topological input.

No `axiom`, `sorry`, `opaque`, `admit`, `constant`, or `unsafe` is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Top-degree surjectivity of the cohomology transfer, from the single
vanishing fact.**  This is `cohTransferZMod2_top_surjective` with the cellular
datum replaced by the isolated hypothesis `Hⁿ⁺¹(RPⁿ; F₂) = 0`. -/
theorem cohTransferZMod2_top_surjective_of_vanish (n : ℕ)
    (hvanish : IsZero (rpCohomology n (n + 1))) :
    Function.Surjective (cohTransferZMod2 n n).hom := by
  have hSE := transferSEScoch_shortExact n
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := rfl
  have hexact := hSE.homology_exact₃ n (n + 1) hrel
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  have hzero : IsZero ((transferSEScoch n).X₁.homology (n + 1)) := by
    rw [transferSEScoch_X₁_homology]
    exact hvanish
  haveI hsub : Subsingleton ((transferSEScoch n).X₁.homology (n + 1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp hzero
  intro y
  obtain ⟨x, hx⟩ := hexact y (Subsingleton.elim _ _)
  refine ⟨x, ?_⟩
  rw [← transferSEScoch_homologyMap_g n n]
  exact hx

/-- **`dim Hⁿ(RPⁿ; F₂) = 1`, from the single vanishing fact.**  The transfer
`Hⁿ(Sⁿ; F₂) ↠ Hⁿ(RPⁿ; F₂)` is surjective, so `dim Hⁿ(RPⁿ) ≤ dim Hⁿ(Sⁿ) = 1`;
the unconditional `αⁿ ≠ 0` makes `Hⁿ(RPⁿ)` nontrivial, so `dim ≥ 1`. -/
theorem rpCohomology_top_finrank_one_of_vanish (n : ℕ) (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1))) :
    Module.finrank (ZMod 2) (rpCohomology n n) = 1 := by
  -- Let `T := (cohTransferZMod2 n n).hom`.
  set T : sphereCohomology n n →ₗ[ZMod 2] rpCohomology n n := (cohTransferZMod2 n n).hom;
  -- By `Step B (upper bound)`, we have `finrank (rpCohomology n n) ≤ 1`.
  have h_finrank_le_one : Module.finrank (ZMod 2) (rpCohomology n n) ≤ 1 := by
    have h_finrank_le_one : Module.finrank (ZMod 2) (rpCohomology n n) ≤ Module.finrank (ZMod 2) (sphereCohomology n n) := by
      have hsurj := cohTransferZMod2_top_surjective_of_vanish n hvanish;
      have hfinrank_le : FiniteDimensional (ZMod 2) (sphereCohomology n n) := by
        exact FiniteDimensional.of_finrank_eq_succ
          (sphere_top_cohomology_finrank_one_direct n hn)
      have := LinearMap.finrank_range_add_finrank_ker T;
      rw [ ← this, LinearMap.range_eq_top.mpr hsurj ] ; norm_num;
    exact h_finrank_le_one.trans (by rw [sphere_top_cohomology_finrank_one_direct n hn])
  refine' le_antisymm h_finrank_le_one ( Nat.pos_of_ne_zero _ );
  have h_nontrivial : Nontrivial (rpCohomology n n) := by
    exact ⟨ _, _, actualRPAlpha_topPower_ne_zero_no_cup n hn ⟩;
  apply_rules [ Module.finrank_pos.ne' ];
  have h_finite : Module.Finite (ZMod 2) (sphereCohomology n n) := by
    exact Module.finite_of_finrank_pos
      (by linarith [sphere_top_cohomology_finrank_one_direct n hn])
  exact Module.Finite.of_surjective T ( cohTransferZMod2_top_surjective_of_vanish n hvanish )

/-- **Top-degree injectivity of the cohomology transfer, from the single
vanishing fact.**  A surjection between the equal one-dimensional `F₂`-spaces
`Hⁿ(Sⁿ)` and `Hⁿ(RPⁿ)` is injective. -/
theorem cohTransferZMod2_top_injective_of_vanish (n : ℕ) (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1))) :
    Function.Injective (cohTransferZMod2 n n).hom := by
  have hsph : Module.finrank (ZMod 2) (sphereCohomology n n) = 1 :=
    sphere_top_cohomology_finrank_one_direct n hn
  have hrp : Module.finrank (ZMod 2) (rpCohomology n n) = 1 :=
    rpCohomology_top_finrank_one_of_vanish n hn hvanish
  haveI : FiniteDimensional (ZMod 2) (sphereCohomology n n) :=
    FiniteDimensional.of_finrank_eq_succ hsph
  haveI : FiniteDimensional (ZMod 2) (rpCohomology n n) :=
    FiniteDimensional.of_finrank_eq_succ hrp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsph.trans hrp.symm)).2
    (cohTransferZMod2_top_surjective_of_vanish n hvanish)

/-- **The double-cover top-class transfer predicate, from the single vanishing
fact.**  `RPnTopClassTransfer n` is obtained directly from the transfer being a
linear isomorphism in the top degree (surjective and injective) plus the transfer
naturality square for descended odd maps.  No `RPnCellularCochainStructure n` and
no `TopHomologyTransferNonzeroWitness n` are used. -/
theorem construct_RPnTopClassTransfer_of_topVanish (n : ℕ) (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1))) :
    RPnTopClassTransfer n := by
  intro f hf a ha_fixed ha_nonzero
  obtain ⟨c, hc⟩ : ∃ c, (cohTransferZMod2 n n).hom c = a := by
    exact cohTransferZMod2_top_surjective_of_vanish n hvanish a
  use c
  constructor
  ·
    aesop
  ·
    apply (cohTransferZMod2_top_injective_of_vanish n hn hvanish);
    have := rpToSphereTransfer_naturality_odd ( n := n ) ( k := n ) f hf; replace := congr_arg ( fun e => e.hom c ) this; aesop;

/-- **`OddMapFixesTopClass n` from `hn` and the single vanishing fact.**  Every
odd self-map of `Sⁿ` fixes a nonzero top `F₂`-class, with the only remaining
honest input the RPⁿ top-dimension vanishing `Hⁿ⁺¹(RPⁿ; F₂) = 0`.  The previously
monolithic `htop : OddMapFixesTopClass n` hypothesis is *not* reintroduced. -/
theorem oddMapFixesTopClass_of_topVanish (n : ℕ) (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1))) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_actualTopPower_and_transfer hn
    (construct_RPnTopClassTransfer_of_topVanish n hn hvanish)

/-- **Unconditional top-class fixedness.** Every odd self-map of `Sⁿ`, for
`n ≥ 1`, fixes a nonzero top mod-two cohomology class. -/
theorem oddMapFixesTopClass_unconditional (n : ℕ) (hn : 1 ≤ n) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_topVanish n hn
    (rpCohomology_topPlusOne_isZero_direct n)

/-- Closed endpoint for unconditional odd-map top-class fixedness. -/
theorem oddMapFixesTopClass_unconditional_closed :
    (∀ n : ℕ, 1 ≤ n → OddMapFixesTopClass n) ∧
    (∀ n : ℕ, IsZero (rpCohomology n (n + 1))) :=
  ⟨oddMapFixesTopClass_unconditional,
    rpCohomology_topPlusOne_isZero_direct⟩

#audit_closed_axioms oddMapFixesTopClass_unconditional_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
