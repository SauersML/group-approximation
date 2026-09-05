import GroupApproximation.CharClass.ThomPuncturedCover
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# The punctured-product recursion `H^k(N ∖ z; F₂) = 0` for `k ≥ dim N`

Step C of the LIX obstruction (`notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3) needs
that the restriction `j^* : H^{2r}(N, N ∖ z) → H^{2r}(N)` is an isomorphism for
`N = S¹ × S⁵ × ∏_j CP(d_j)` and `2r = dim N`.  Surjectivity of `j^*` comes from
the long exact sequence of the pair together with

> `H^k(N ∖ z; F₂) = 0` for every `k ≥ dim N`.

This file proves that vanishing for every space built from "top-punctured
acyclic" pieces by finite products.  The induction is Mayer–Vietoris for the
cover of `ThomPuncturedCover.lean`,

```text
(X × Y) ∖ {(x₀, y₀)}  =  ((X ∖ x₀) × Y)  ∪  (X × (Y ∖ y₀)),
    intersection      =   (X ∖ x₀) × (Y ∖ y₀),
```

together with the *vanishing form* of the Künneth theorem: if `H^{>p}(A) = 0` and
`H^{>q}(B) = 0` then `H^{>p+q}(A × B) = 0`.  Both are peer facts
(`cc-cohom-api`, needs (A1)–(A3) of `notes/lix-lane-reports/cc-thom.md`); until
they land they are the three fields of `CohomologyToolkit`, a `Prop`-valued
structure — not an `axiom`, not a `sorry`.  When they land, one term
`⟨isZero_cohomology_of_cover, isZero_cohomology_prod, …⟩` instantiates every
result below.

## The bookkeeping

`PuncturedAcyclic Z d z` says: `Z` has formal dimension `d ≥ 1`, its cohomology
vanishes *above* `d`, and the cohomology of `Z ∖ z` vanishes *from* `d` on.  The
two base cases of the LIX application are

* `Z = S^n`, `n ≥ 1`, `d = n`: `S^n ∖ pt` is contractible, so its cohomology
  vanishes in every positive degree, `n` included;
* `Z = CP(d')`, `d' ≥ 1`, `d = 2 d'`: `CP(d') ∖ pt ≃ CP(d'−1)`, whose cohomology
  vanishes above `2d' − 2`, hence from `2d'` on.

Both are `cc-projective` deliverables ((D2)–(D4)); the recursion here is what
turns them into the statement for the product.

## Main results

* `PuncturedAcyclic.prod` — the recursion step.
* `PuncturedAcyclic.isZero_punctured_top` — the conclusion actually consumed by
  Step C.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The three facts about mod-2 singular cohomology that the punctured-product
recursion consumes.  Each is a `cc-cohom-api` deliverable; see
`notes/lix-lane-reports/cc-thom.md` §3, needs (A1), (A2), (A3). -/
structure CohomologyToolkit : Prop where
  /-- **Mayer–Vietoris, vanishing form** (need (A1)).  For a two-element open cover of
  `Z`, vanishing of `H^m` on the intersection and of `H^{m+1}` on the two pieces forces
  `H^{m+1}(Z) = 0`. -/
  mv : ∀ (Z : Type) [TopologicalSpace Z] (U V : Opens Z), U ⊔ V = ⊤ → ∀ m : ℕ,
    IsZero (cohomologyZMod2 (TopCat.of ↥(U ⊓ V)) m) →
    IsZero (cohomologyZMod2 (TopCat.of ↥U) (m + 1)) →
    IsZero (cohomologyZMod2 (TopCat.of ↥V) (m + 1)) →
    IsZero (cohomologyZMod2 (TopCat.of Z) (m + 1))
  /-- **Künneth, vanishing form** (need (A2)).  Cohomology of a product vanishes above
  the sum of two degrees above which the factors' cohomology vanishes. -/
  kunneth : ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (p q : ℕ),
    (∀ a, p < a → IsZero (cohomologyZMod2 (TopCat.of A) a)) →
    (∀ b, q < b → IsZero (cohomologyZMod2 (TopCat.of B) b)) →
    ∀ k, p + q < k → IsZero (cohomologyZMod2 (TopCat.of (A × B)) k)
  /-- **Homeomorphism invariance** (need (A3)), in transport form. -/
  homeo : ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B], (A ≃ₜ B) → ∀ n : ℕ,
    IsZero (cohomologyZMod2 (TopCat.of B) n) → IsZero (cohomologyZMod2 (TopCat.of A) n)
  /-- **Homotopy-equivalence invariance** (need (A4)), in transport form.  Used for the
  base case `CP(d+1) ∖ pt ≃ CP(d)`. -/
  homotopy : ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B],
    ContinuousMap.HomotopyEquiv A B → ∀ n : ℕ,
    IsZero (cohomologyZMod2 (TopCat.of B) n) → IsZero (cohomologyZMod2 (TopCat.of A) n)
  /-- **Contractible spaces have no positive-degree cohomology** (need (A5)).  Used for the
  base case `S^n ∖ pt ≃ pt`. -/
  contractible : ∀ (A : Type) [TopologicalSpace A], ContractibleSpace A → ∀ n : ℕ, 0 < n →
    IsZero (cohomologyZMod2 (TopCat.of A) n)

/-- **Top-punctured acyclicity.**  `Z` has formal dimension `d ≥ 1`, its mod-2
cohomology vanishes strictly above `d`, and the mod-2 cohomology of the complement of
the distinguished point `z` vanishes from `d` on.

Spheres `S^n` (`n ≥ 1`, `d = n`) and complex projective spaces `CP(d')` (`d' ≥ 1`,
`d = 2d'`) satisfy this; `PuncturedAcyclic.prod` propagates it through products. -/
structure PuncturedAcyclic (Z : Type) [TopologicalSpace Z] (d : ℕ) (z : Z) : Prop where
  /-- The formal dimension is positive.  (A point would break the recursion: `pt ∖ pt`
  is empty, but `H^0(pt) ≠ 0`, and the Künneth bookkeeping below subtracts one.) -/
  pos : 0 < d
  /-- Cohomology vanishes above the formal dimension. -/
  vanish : ∀ k, d < k → IsZero (cohomologyZMod2 (TopCat.of Z) k)
  /-- Cohomology of the punctured space vanishes from the formal dimension on. -/
  puncturedVanish : ∀ k, d ≤ k →
    IsZero (cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set Z)) k)

/-- **Base case, contractible puncture.**  A space of positive formal dimension `d` whose
cohomology vanishes above `d` and whose puncture is contractible is top-punctured acyclic.

This is the sphere case: `S^n ∖ pt` is contractible (stereographic projection, see
`ThomPuncturedSphere.lean`), and `H^k(S^n) = 0` for `k > n`. -/
theorem puncturedAcyclic_of_contractible (T : CohomologyToolkit)
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hd : 0 < d) {z : Z}
    (hvanish : ∀ k, d < k → IsZero (cohomologyZMod2 (TopCat.of Z) k))
    (hcontr : ContractibleSpace ↥({z}ᶜ : Set Z)) :
    PuncturedAcyclic Z d z :=
  ⟨hd, hvanish, fun _ hk => T.contractible _ hcontr _ (lt_of_lt_of_le hd hk)⟩

/-- **Base case, puncture homotopy equivalent to a smaller space.**  This is the projective
case: `CP(d') ∖ pt ≃ CP(d'−1)`, whose cohomology vanishes above `2d' − 2 < 2d'`.

`hdW : dW < d` is where "puncturing drops the dimension" enters. -/
theorem puncturedAcyclic_of_homotopyEquiv (T : CohomologyToolkit)
    {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W] {d dW : ℕ} (hd : 0 < d) {z : Z}
    (hvanish : ∀ k, d < k → IsZero (cohomologyZMod2 (TopCat.of Z) k))
    (e : ContinuousMap.HomotopyEquiv ↥({z}ᶜ : Set Z) W)
    (hW : ∀ k, dW < k → IsZero (cohomologyZMod2 (TopCat.of W) k))
    (hdW : dW < d) :
    PuncturedAcyclic Z d z :=
  ⟨hd, hvanish, fun k hk => T.homotopy _ _ e k (hW k (lt_of_lt_of_le hdW hk))⟩

namespace PuncturedAcyclic

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The punctured-product recursion.**  If `X` and `Y` are top-punctured acyclic of
dimensions `dX` and `dY`, so is `X × Y`, of dimension `dX + dY`, punctured at
`(x₀, y₀)`.

The `vanish` half is Künneth.  The `puncturedVanish` half is Mayer–Vietoris for the
cover of `ThomPuncturedCover.lean`: writing `k = m + 1`,

* the intersection is `(X ∖ x₀) × (Y ∖ y₀)`, whose cohomology vanishes above
  `(dX − 1) + (dY − 1) = dX + dY − 2 ≤ m − 1`, in particular in degree `m`;
* the left piece is `(X ∖ x₀) × Y`, whose cohomology vanishes above
  `(dX − 1) + dY = dX + dY − 1 ≤ m`, in particular in degree `m + 1`;
* the right piece is symmetric.

Note where positivity of `dX` and `dY` is used: it is exactly the `−1` in the first
Künneth exponent, i.e. the fact that puncturing drops the top degree. -/
theorem prod [T1Space X] [T1Space Y] (T : CohomologyToolkit)
    {dX dY : ℕ} {x₀ : X} {y₀ : Y}
    (hX : PuncturedAcyclic X dX x₀) (hY : PuncturedAcyclic Y dY y₀) :
    PuncturedAcyclic (X × Y) (dX + dY) (x₀, y₀) := by
  have hxpos := hX.pos
  have hypos := hY.pos
  refine ⟨by omega, fun k hk => T.kunneth X Y dX dY hX.vanish hY.vanish k hk, ?_⟩
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine T.mv (puncturedProd x₀ y₀) (leftOpens x₀ y₀) (rightOpens x₀ y₀)
    (leftOpens_sup_rightOpens x₀ y₀) m ?_ ?_ ?_
  · refine T.homeo _ _ (interOpensHomeo x₀ y₀) m ?_
    refine T.kunneth _ _ (dX - 1) (dY - 1) (fun a ha => hX.puncturedVanish a (by omega))
      (fun b hb => hY.puncturedVanish b (by omega)) m (by omega)
  · refine T.homeo _ _ (leftOpensHomeo x₀ y₀) (m + 1) ?_
    refine T.kunneth _ _ (dX - 1) dY (fun a ha => hX.puncturedVanish a (by omega))
      hY.vanish (m + 1) (by omega)
  · refine T.homeo _ _ (rightOpensHomeo x₀ y₀) (m + 1) ?_
    refine T.kunneth _ _ dX (dY - 1) hX.vanish
      (fun b hb => hY.puncturedVanish b (by omega)) (m + 1) (by omega)

/-- The conclusion Step C consumes: the punctured space has no cohomology in the top
degree of the unpunctured one. -/
theorem isZero_punctured_top {Z : Type} [TopologicalSpace Z] {d : ℕ} {z : Z}
    (h : PuncturedAcyclic Z d z) :
    IsZero (cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set Z)) d) :=
  h.puncturedVanish d le_rfl

/-- The same, as a `Subsingleton` statement, which is the form in which
`ThomFieldTwo.surjective_of_exact_of_subsingleton` takes it. -/
theorem subsingleton_punctured_top {Z : Type} [TopologicalSpace Z] {d : ℕ} {z : Z}
    (h : PuncturedAcyclic Z d z) :
    Subsingleton (cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set Z)) d) :=
  ModuleCat.subsingleton_of_isZero h.isZero_punctured_top

end PuncturedAcyclic

end GroupApproximation.CharClass
