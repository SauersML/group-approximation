import GroupApproximation.CharClass.LIXKStepC
import GroupApproximation.CharClass.LIXKSection
import GroupApproximation.CharClass.LIXKPunctured
import GroupApproximation.CharClass.LIXStepCOddRelative
import GroupApproximation.CharClass.LIXStepEPunctured
import GroupApproximation.CharClass.LIXExcisionChart
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C's odd side with `k+1` zeros, wired to the LIX objects

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4, items 1, 2 and 5 of the first
deliverable).

`CharClass/LIXStepCOddWired.lean`'s `lix_topClass_ne_zero_of_three` is the one-zero Step C
at the LIX objects, over the three open hypotheses `hsq`, `hres`, `hclass`.  This file is
its `k`-zero counterpart: `lixK_topClass_ne_zero` over four, with `k` an explicit
parameter and the exponent `k + 1`.

## What is wired here, and what is left open

Wired and unconditional:

* the section with `a = e₁` and `b = Ψ_k ∘ x`, its `k+1` zeros and their distinctness
  (`CharClass/LIXKSection.lean`);
* the section as a map of pairs into the punctured total space, at the `k+1`-punctured
  base (`lixKSectionTotal_mapsTo` below);
* the `k+1` restriction maps `ρ_i` and their compatibility `ρ_i ≫ j = j_i`, which is
  naturality of `relToAbs` along the **identity** of `N` (`lixK_hcompat`);
* the `k+1`-point punctured vanishing (`puncturedVanish_lixKZeroSet`), from
  `CharClass/LIXKPunctured.lean`;
* the count and the parity, from `CharClass/LIXKCount.lean`.

Left open, each a binder of the theorem below with a named owner:

* `hsplit : LocalSplit …` — the splitting.  Its route is **relative Mayer–Vietoris**, not
  excision to disjoint balls: `CharClass/LIXKRelativeMV.lean` proves the cochain-level
  statement, and an induction on the punctures turns it into `LocalSplit`;
* `hloc : LocalClassesAgree …` — at `p = 2` this is discharged with no transport at all by
  `CharClass/LIXKStepCTwo.lean`, since an `F₂`-line has a unique nonzero element; at odd `p`
  it is `sp-design` §4.1's Half A and Half B;
* `hx : xloc i₀ ≠ 0` and the line data `exc`, `chartIso` — the one-zero local computation
  at `−e₁` rather than at `−e₃`, i.e. the existing `LIXSectionChart`/`LIXHsq*` chain with
  the constant section as a parameter;
* `hclass` — the Thom class, exactly as at one zero.

## Main declarations

* `lixKSectionTotal`, `lixKSectionTotal_mapsTo`, `lixKSRel` — the section as a map of
  pairs at the `k+1`-punctured base.
* `lixKJ`, `lixKJloc`, `lixKRho`, `lixK_hcompat` — the maps the count consumes.
* `puncturedVanish_lixKZeroSet` — `H^{2r}(N ∖ Z; F₂) = 0` for the `k+1` zeros.
* `lixK_topClass_ne_zero` — **the `k`-zero Step C at the LIX objects.**
* `lixK_topClass_ne_zero_odd` — the same with the exponent `e = k + 1` and `Odd e`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The base pair with `k+1` punctures, and the `k+1` restrictions -/

/-- `j` for the `k+1`-punctured pair. -/
def lixKJ (k : ℕ) (dd : Fin ℓ → ℕ) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) n ⟶
      cohomologyZMod2 (lixN dd) n :=
  relToAbs (ZMod 2) (lixN dd) ((lixKZeroSet k dd)ᶜ) n

/-- `j_i` for the single-puncture pair at the `i`-th zero. -/
def lixKJloc (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd)) n ⟶
      cohomologyZMod2 (lixN dd) n :=
  relToAbs (ZMod 2) (lixN dd) ({lixKZero k dd i}ᶜ) n

/-- `i`: restriction to the complement of the `i`-th zero. -/
def lixKI (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (n : ℕ) :
    cohomologyZMod2 (lixN dd) n ⟶
      cohomologyZMod2 (TopCat.of ↥({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd))) n :=
  absToSub (X := lixN dd) (ZMod 2) ({lixKZero k dd i}ᶜ) n

/-- Exactness of the pair sequence at the absolute group, at the `i`-th zero. -/
theorem lixK_hexact (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (n : ℕ) :
    LinearMap.range (lixKJloc k dd i n).hom = LinearMap.ker (lixKI k dd i n).hom :=
  relLES_range_eq_ker (lixN dd) ({lixKZero k dd i}ᶜ) n

/-- The identity of `N` is a map of pairs from the `k+1`-punctured pair to the pair
punctured at the `i`-th zero only, because the complement of all the zeros is inside the
complement of one of them. -/
theorem lixK_mapsTo (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ∀ x ∈ ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)),
      (ConcreteCategory.hom (𝟙 (lixN dd))) x ∈
        ({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd)) := by
  intro x hx
  show x ∉ ({lixKZero k dd i} : Set (↥sphereOne × baseM dd))
  intro hmem
  exact hx ((mem_lixKZeroSet_iff k dd x).mpr ⟨i, hmem⟩)

/-- `ρ_i`, the relative pullback along that map of pairs. -/
def lixKRho (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd)) n ⟶
      relCohomology (ZMod 2) (lixN dd)
        ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) n :=
  relPullback (ZMod 2) (𝟙 (lixN dd)) (lixK_mapsTo k dd i) n

/-- **`ρ_i ≫ j = j_i`.**  This is naturality of `relToAbs` along the identity of the
ambient space, so it costs one rewrite and no geometry. -/
theorem lixK_hcompat (k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (n : ℕ) :
    lixKRho k dd i n ≫ lixKJ k dd n = lixKJloc k dd i n := by
  have h : lixKJloc k dd i n ≫ RelativeSupport.absPull (𝟙 (lixN dd)) n
      = lixKRho k dd i n ≫ lixKJ k dd n :=
    relToAbs_naturality (ZMod 2) (𝟙 (lixN dd)) (lixK_mapsTo k dd i) n
  rw [RelativeSupport.absPull_id_eq, Category.comp_id] at h
  exact h.symm

/-! ## 2. The section as a map of pairs -/

/-- The `k`-fold section, into the total space of the bundle. -/
def lixKSectionTotal (k : ℕ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    C(↥sphereOne × baseM dd, Bundle.Total (lixBundle G hGc hGu)) where
  toFun x := ⟨(x, lixKSection k G x), lixKSection_mem k hGu x⟩
  continuous_toFun :=
    (continuous_id.prodMk (lixKSection_continuous hGc hGu hGe)).subtype_mk _

/-- **The section carries the `k+1`-punctured base into the punctured total space.** -/
theorem lixKSectionTotal_mapsTo (k : ℕ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    ∀ x ∈ ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)),
      (ConcreteCategory.hom (cmap (lixKSectionTotal k hGc hGu hGe))) x ∈
        lixPuncturedInTotal hGc hGu := by
  intro x hx
  refine ⟨lixKSection_mem k hGu x, ?_⟩
  intro hzero
  exact lixKSection_ne_zero_of_notMem hGe hx hzero

/-- `sRel` at the `k+1`-punctured base. -/
def lixKSRel (k : ℕ) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) (n : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n ⟶
      relCohomology (ZMod 2) (lixN dd)
        ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) n :=
  relPullback (ZMod 2) (cmap (lixKSectionTotal k hGc hGu hGe))
    (lixKSectionTotal_mapsTo k hGc hGu hGe) n

/-- The section, as a morphism of spaces. -/
def lixKS (k : ℕ) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    lixN dd ⟶ lixTotalPair hGc hGu :=
  cmap (lixKSectionTotal k hGc hGu hGe)

/-- `sAbs` for the `k`-fold section. -/
def lixKSAbs (k : ℕ) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) (n : ℕ) :
    RelativeSupport.lixHE hGc hGu n ⟶ cohomologyZMod2 (lixN dd) n :=
  RelativeSupport.absPull (lixKS k hGc hGu hGe) n

theorem lixKS_comp_lixPi (k : ℕ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    lixKS k hGc hGu hGe ≫ RelativeSupport.lixPi hGc hGu = 𝟙 (lixN dd) := rfl

/-- `hnat` for the `k`-fold section. -/
theorem lixK_hnat (k : ℕ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) (n : ℕ) :
    lixKSRel k hGc hGu hGe n ≫ lixKJ k dd n
      = RelativeSupport.lixJE hGc hGu n ≫ lixKSAbs k hGc hGu hGe n :=
  (relToAbs_naturality (ZMod 2) (lixKS k hGc hGu hGe)
    (lixKSectionTotal_mapsTo k hGc hGu hGe) n).symm

/-- `hsection` for the `k`-fold section. -/
theorem lixK_hsection (k : ℕ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) (n : ℕ) :
    RelativeSupport.lixPiStar hGc hGu n ≫ lixKSAbs k hGc hGu hGe n
      = 𝟙 (cohomologyZMod2 (lixN dd) n) := by
  rw [RelativeSupport.lixPiStar, lixKSAbs, ← RelativeSupport.absPull_comp,
    lixKS_comp_lixPi, RelativeSupport.absPull_id_eq]

/-! ## 3. Punctured acyclicity, at every point and at the `k+1` zeros -/

/-- The LIX base is top-punctured acyclic at **every** point, not only at the manuscript's
zero.  The producer already took the point as an argument; this only names the fact. -/
theorem puncturedAcyclic_lixPoint
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j) (w : ↥sphereOne × baseM dd) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd) w := by
  have h := puncturedAcyclic_lixBase_lixTopDegree hCPacyclic kCP kCPpunct hbase dd hdd w
  rwa [lixTopDegree_eq_two_mul_lixRank] at h

/-- **The `k+1`-point punctured vanishing at the LIX base.**  `sp-design` §4.2 item 1.

Not consumed by `lixK_topClass_ne_zero` — see `CharClass/LIXKStepC.lean`'s header for why
the naturality square removes it from the critical path — but it is what makes `j` on the
`k+1`-punctured pair surjective, and any arrangement of the argument that identifies `γ_r`
through exactness rather than through the section needs it. -/
theorem puncturedVanish_lixKZeroSet (k : ℕ)
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j) {m : ℕ} (hm : 2 * lixRank dd ≤ m) :
    IsZero (cohomologyZMod2
      (TopCat.of ↥((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd))) m) :=
  isZero_punctured_finite
    (puncturedAcyclic_lixPoint hCPacyclic kCP kCPpunct hbase hdd) hm
    (finite_lixKZeroSet k dd) (lixKZeroSet_nonempty k dd)

/-! ## 4. Step C's odd side with `k+1` zeros, at the LIX objects -/

/-- **Step C's odd side with `k+1` zeros.**

The shape of `LIXStepCOddWired.lix_topClass_ne_zero_of_three`, with `k` an explicit
parameter and four open hypotheses instead of three.  Every remaining binder is either the
one-zero Step C's own, taken at the distinguished zero `z_{i₀}`, or one of the two `k`-zero
obligations named in `CharClass/LIXKCount.lean`.

The parity enters in exactly one place, `hk`, and it is a statement about the coefficient
field: `k + 1` must be invertible in `F₂`, i.e. odd. -/
theorem lixK_topClass_ne_zero (k : ℕ) (i₀ : Fin (k + 1))
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0)
    (hacyclic : PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd)
      (lixKZero k dd i₀))
    (absLine : Nonempty
      (cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2))
    {chart : ModuleCat.{0} (ZMod 2)}
    (exc : relCohomology (ZMod 2) (lixN dd)
      ({lixKZero k dd i₀}ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd) ≅ chart)
    (chartIso : chart ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
      (puncturedSet (lixRank dd)) (2 * lixRank dd))
    {u : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN dd)
      ({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd)}
    (hsplit : LocalSplit (fun i => lixKRho k dd i (2 * lixRank dd))
      ((lixKSRel k hGc hGu hGe (2 * lixRank dd)).hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hloc : LocalClassesAgree (fun i => lixKJloc k dd i (2 * lixRank dd)) xloc c)
    (hk : ((k + 1 : ℕ) : ZMod 2) ≠ 0)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : (RelativeSupport.lixJE hGc hGu (2 * lixRank dd)).hom u
      = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd)).hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_kzero_naturality hacyclic i₀
    (lixKJ k dd (2 * lixRank dd))
    (fun i => lixKRho k dd i (2 * lixRank dd))
    (fun i => lixKJloc k dd i (2 * lixRank dd))
    (fun i => lixK_hcompat k dd i (2 * lixRank dd))
    (lixKI k dd i₀ (2 * lixRank dd))
    (lixK_hexact k dd i₀ (2 * lixRank dd))
    absLine exc chartIso
    (RelativeSupport.lixJE hGc hGu (2 * lixRank dd))
    (lixKSRel k hGc hGu hGe (2 * lixRank dd))
    (lixKSAbs k hGc hGu hGe (2 * lixRank dd))
    (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd))
    (lixK_hnat k hGc hGu hGe (2 * lixRank dd))
    (lixK_hsection k hGc hGu hGe (2 * lixRank dd))
    hsplit hx hloc hk hclass

/-- **The exponent-facing form.**  With `e = k + 1` the statement reads: for every odd
exponent `e ≥ 1`, the `e`-fold section's top Chern class is nonzero.  This is the
`p = 2` instance of the strengthening's "every odd power of the witness stays outside
`U₀`". -/
theorem lixK_topClass_ne_zero_odd (k : ℕ) (hodd : Odd (k + 1)) (i₀ : Fin (k + 1))
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0)
    (hacyclic : PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd)
      (lixKZero k dd i₀))
    (absLine : Nonempty
      (cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2))
    {chart : ModuleCat.{0} (ZMod 2)}
    (exc : relCohomology (ZMod 2) (lixN dd)
      ({lixKZero k dd i₀}ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd) ≅ chart)
    (chartIso : chart ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
      (puncturedSet (lixRank dd)) (2 * lixRank dd))
    {u : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN dd)
      ({lixKZero k dd i}ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd)}
    (hsplit : LocalSplit (fun i => lixKRho k dd i (2 * lixRank dd))
      ((lixKSRel k hGc hGu hGe (2 * lixRank dd)).hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hloc : LocalClassesAgree (fun i => lixKJloc k dd i (2 * lixRank dd)) xloc c)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : (RelativeSupport.lixJE hGc hGu (2 * lixRank dd)).hom u
      = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd)).hom gamma) :
    gamma ≠ 0 :=
  lixK_topClass_ne_zero k i₀ hGc hGu hGe hacyclic absLine exc chartIso hsplit hx hloc
    (natCast_ne_zero_zmod_two hodd) hclass

/-! Audited on every build. -/

#audit_axioms lixK_hcompat
#audit_axioms puncturedVanish_lixKZeroSet
#audit_axioms lixK_topClass_ne_zero
#audit_axioms lixK_topClass_ne_zero_odd

end GroupApproximation.CharClass
