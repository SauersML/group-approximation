import GroupApproximation.CharClass.ThomPuncturedCover
import GroupApproximation.CharClass.CohomologyBasic
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# The punctured-product recursion `H^k(N ∖ z; K) = 0` for `k ≥ dim N`

Step C of the LIX obstruction (`notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3) needs
that the restriction `j^* : H^{2r}(N, N ∖ z) → H^{2r}(N)` is an isomorphism for
`N = S¹ × S⁵ × ∏_j CP(d_j)` and `2r = dim N`.  Surjectivity of `j^*` comes from
the long exact sequence of the pair together with

> `H^k(N ∖ z; K) = 0` for every `k ≥ dim N`.

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
they land they are the four fields of `CohomologyToolkitOf K`, a `Prop`-valued
structure — not an `axiom`, not a `sorry`.  When they land, one term
`⟨isZero_cohomology_of_cover, isZero_cohomology_prod, …⟩` instantiates every
result below.

## The coefficient ring

Everything in this file is generic in a commutative coefficient ring `K` and none of it
divides, commutes two cup products or uses `1 = -1`: the recursion is Mayer–Vietoris and
bookkeeping, and both inputs arrive as hypotheses.  So the mod-`p` programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5) reuses it verbatim.  `K` is *implicit* in
every theorem here, because the toolkit, the Künneth factor or the acyclicity datum always
determines it; the `ZMod 2` spellings `CohomologyToolkit`, `KunnethFactor`,
`PuncturedAcyclic` are reducible `abbrev`s at the bottom of the file, so the mod-2 answer to
LIX and the fourteen `LIX*` files that name one of the three are byte-unchanged.

What is *not* generic yet, and does not belong here, is the instantiation: the toolkit's
four fields at `K` need homotopy invariance and the contractible-space vanishing over `K`,
which is sp-coeff's Kronecker/universal-coefficients port.  The machine is available now;
its `F₂` instance lives in `ThomToolkitInstance.lean`.

## The bookkeeping

`PuncturedAcyclicOf K Z d z` says: `Z` has formal dimension `d ≥ 1`, its cohomology
vanishes *above* `d`, and the cohomology of `Z ∖ z` vanishes *from* `d` on.  The
two base cases of the LIX application are

* `Z = S^n`, `n ≥ 1`, `d = n`: `S^n ∖ pt` is contractible, so its cohomology
  vanishes in every positive degree, `n` included;
* `Z = CP(d')`, `d' ≥ 1`, `d = 2 d'`: `CP(d') ∖ pt ≃ CP(d'−1)`, whose cohomology
  vanishes above `2d' − 2`, hence from `2d'` on.

Both are `cc-projective` deliverables ((D2)–(D4)); the recursion here is what
turns them into the statement for the product.

## Main results

* `PuncturedAcyclicOf.prod` — the recursion step.
* `PuncturedAcyclicOf.isZero_punctured_top` — the conclusion actually consumed by
  Step C.
* `CohomologyToolkit`, `KunnethFactor`, `PuncturedAcyclic` — the `ZMod 2` spellings.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- `IsZero` transports along a linear equivalence.  This is the bridge from
`cc-cohom-api`'s `pullEquivOfHomeomorph` / `pullEquivOfHomotopyEquiv`, which deliver
`LinearEquiv`s, to the `IsZero` shape in which `CohomologyToolkitOf` states its fields. -/
theorem thomIsZero_of_linearEquiv {R : Type} [Ring R] {M N : ModuleCat.{0} R}
    (e : M ≃ₗ[R] N) (h : IsZero N) : IsZero M := by
  haveI : Subsingleton N := ModuleCat.subsingleton_of_isZero h
  haveI : Subsingleton M := ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton M

/-- The four facts about singular cohomology with coefficients in `K` that the
punctured-product recursion consumes.  The Künneth input is *not* here: it is
`KunnethFactorOf`, taken one factor at a time (see its docstring for why fully general
Künneth is unreachable).  Each is a `cc-cohom-api` deliverable at `K = ZMod 2`; see
`notes/lix-lane-reports/cc-thom.md` §3, needs (A1), (A2), (A3). -/
structure CohomologyToolkitOf (K : Type) [CommRing K] : Prop where
  /-- **Mayer–Vietoris, vanishing form** (need (A1)).  For a two-element open cover of
  `Z`, vanishing of `H^m` on the intersection and of `H^{m+1}` on the two pieces forces
  `H^{m+1}(Z) = 0`. -/
  mv : ∀ (Z : Type) [TopologicalSpace Z] (U V : Opens Z), U ⊔ V = ⊤ → ∀ m : ℕ,
    IsZero (Hmod K (TopCat.of ↥(U ⊓ V)) m) →
    IsZero (Hmod K (TopCat.of ↥U) (m + 1)) →
    IsZero (Hmod K (TopCat.of ↥V) (m + 1)) →
    IsZero (Hmod K (TopCat.of Z) (m + 1))
  /-- **Homeomorphism invariance** (need (A3)), in transport form. -/
  homeo : ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B], (A ≃ₜ B) → ∀ n : ℕ,
    IsZero (Hmod K (TopCat.of B) n) → IsZero (Hmod K (TopCat.of A) n)
  /-- **Homotopy-equivalence invariance** (need (A4)), in transport form.  Used for the
  base case `CP(d+1) ∖ pt ≃ CP(d)`. -/
  homotopy : ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B],
    ContinuousMap.HomotopyEquiv A B → ∀ n : ℕ,
    IsZero (Hmod K (TopCat.of B) n) → IsZero (Hmod K (TopCat.of A) n)
  /-- **Contractible spaces have no positive-degree cohomology** (need (A5)).  Used for the
  base case `S^n ∖ pt ≃ pt`. -/
  contractible : ∀ (A : Type) [TopologicalSpace A], ContractibleSpace A → ∀ n : ℕ, 0 < n →
    IsZero (Hmod K (TopCat.of A) n)

/-- **Künneth vanishing for one fixed second factor `Y`.**

`cc-cohom-api` established that fully general Künneth is *not* reachable here: it needs
Eilenberg–Zilber, a chain equivalence `C_*(A × B) ≃ C_*(A) ⊗ C_*(B)`, which neither the
vendored tree nor Mathlib has.  What is reachable is the statement with the second
factor fixed to a sphere (`cc-cohom-api`, by Mayer–Vietoris on the hemispheres) or to a
`CP(d)` (`cc-projective`).  So the recursion asks for exactly that, one factor at a
time, and never for a product of two general spaces.

Arranging `N` as a **left-nested** product `(((S¹ × S⁵) × CP(d₁)) × CP(d₂)) × ⋯` makes
every second factor either a sphere, a `CP(d)`, a punctured sphere (contractible, and
then `kunnethFactor_of_prodEquiv` applies with no Künneth at all) or a punctured
`CP(d)` (homotopy equivalent to `CP(d−1)`, so again a `CP`).

The factor carries its own dimension `q` as an index rather than as a hypothesis,
because that is the shape in which the theorem is provable: `cc-cohom-api`'s green
`isZero_cohomology_prod_sphere` fixes `q` to the sphere's dimension. -/
structure KunnethFactorOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (q : ℕ) : Prop where
  /-- Cohomology of `A × Y` vanishes above `p + q` whenever that of `A` vanishes above
  `p`. -/
  prod : ∀ (A : Type) [TopologicalSpace A] (p : ℕ),
    (∀ a, p < a → IsZero (Hmod K (TopCat.of A) a)) →
    ∀ k, p + q < k → IsZero (Hmod K (TopCat.of (A × Y)) k)

/-- A Künneth factor of dimension `q` is one of any larger dimension. -/
theorem KunnethFactorOf.mono {K : Type} [CommRing K] {Y : Type} [TopologicalSpace Y]
    {q q' : ℕ} (h : KunnethFactorOf K Y q) (hq : q ≤ q') : KunnethFactorOf K Y q' :=
  ⟨fun A _ p hA k hk => h.prod A p hA k (by omega)⟩

/-- **A cohomologically invisible factor is a Künneth factor.**  If `H^n(A × Y) ≅ H^n(A)`
naturally in `A` and `n` — which is `cc-cohom-api`'s `cohProdContractible` whenever `Y`
is contractible — then `Y` is a Künneth factor.  This is what covers the punctured
spheres, where no Künneth theorem is needed at all. -/
theorem kunnethFactor_of_prodEquiv {K : Type} [CommRing K] (Y : Type) [TopologicalSpace Y]
    (e : ∀ (A : Type) [TopologicalSpace A] (n : ℕ),
      Hmod K (TopCat.of A) n ≃ₗ[K] Hmod K (TopCat.of (A × Y)) n) :
    KunnethFactorOf K Y 0 :=
  ⟨fun A _ p hA k hk => thomIsZero_of_linearEquiv (e A k).symm (hA k (by omega))⟩

/-- **Top-punctured acyclicity.**  `Z` has formal dimension `d ≥ 1`, its `K`-cohomology
vanishes strictly above `d`, and the `K`-cohomology of the complement of the distinguished
point `z` vanishes from `d` on.

Spheres `S^n` (`n ≥ 1`, `d = n`) and complex projective spaces `CP(d')` (`d' ≥ 1`,
`d = 2d'`) satisfy this; `PuncturedAcyclicOf.prod` propagates it through products. -/
structure PuncturedAcyclicOf (K : Type) [CommRing K] (Z : Type) [TopologicalSpace Z]
    (d : ℕ) (z : Z) : Prop where
  /-- The formal dimension is positive.  (A point would break the recursion: `pt ∖ pt`
  is empty, but `H^0(pt) ≠ 0`, and the Künneth bookkeeping below subtracts one.) -/
  pos : 0 < d
  /-- Cohomology vanishes above the formal dimension. -/
  vanish : ∀ k, d < k → IsZero (Hmod K (TopCat.of Z) k)
  /-- Cohomology of the punctured space vanishes from the formal dimension on. -/
  puncturedVanish : ∀ k, d ≤ k →
    IsZero (Hmod K (TopCat.of ↥({z}ᶜ : Set Z)) k)

/-- **Base case, contractible puncture.**  A space of positive formal dimension `d` whose
cohomology vanishes above `d` and whose puncture is contractible is top-punctured acyclic.

This is the sphere case: `S^n ∖ pt` is contractible (stereographic projection, see
`ThomPuncturedSphere.lean`), and `H^k(S^n) = 0` for `k > n`. -/
theorem puncturedAcyclic_of_contractible {K : Type} [CommRing K] (T : CohomologyToolkitOf K)
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hd : 0 < d) {z : Z}
    (hvanish : ∀ k, d < k → IsZero (Hmod K (TopCat.of Z) k))
    (hcontr : ContractibleSpace ↥({z}ᶜ : Set Z)) :
    PuncturedAcyclicOf K Z d z :=
  ⟨hd, hvanish, fun _ hk => T.contractible _ hcontr _ (lt_of_lt_of_le hd hk)⟩

/-- **Base case, puncture homotopy equivalent to a smaller space.**  This is the projective
case: `CP(d') ∖ pt ≃ CP(d'−1)`, whose cohomology vanishes above `2d' − 2 < 2d'`.

`hdW : dW < d` is where "puncturing drops the dimension" enters. -/
theorem puncturedAcyclic_of_homotopyEquiv {K : Type} [CommRing K] (T : CohomologyToolkitOf K)
    {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W] {d dW : ℕ} (hd : 0 < d) {z : Z}
    (hvanish : ∀ k, d < k → IsZero (Hmod K (TopCat.of Z) k))
    (e : ContinuousMap.HomotopyEquiv ↥({z}ᶜ : Set Z) W)
    (hW : ∀ k, dW < k → IsZero (Hmod K (TopCat.of W) k))
    (hdW : dW < d) :
    PuncturedAcyclicOf K Z d z :=
  ⟨hd, hvanish, fun k hk => T.homotopy _ _ e k (hW k (lt_of_lt_of_le hdW hk))⟩

namespace PuncturedAcyclicOf

variable {K : Type} [CommRing K] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

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
theorem prod [T1Space X] [T1Space Y] (T : CohomologyToolkitOf K)
    {dX dY : ℕ} {x₀ : X} {y₀ : Y}
    (kY : KunnethFactorOf K Y dY) (kY' : KunnethFactorOf K ↥({y₀}ᶜ : Set Y) (dY - 1))
    (hX : PuncturedAcyclicOf K X dX x₀) (hY : PuncturedAcyclicOf K Y dY y₀) :
    PuncturedAcyclicOf K (X × Y) (dX + dY) (x₀, y₀) := by
  have hxpos := hX.pos
  have hypos := hY.pos
  refine ⟨by omega, fun k hk => kY.prod X dX hX.vanish k hk, ?_⟩
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine T.mv (puncturedProd x₀ y₀) (leftOpens x₀ y₀) (rightOpens x₀ y₀)
    (leftOpens_sup_rightOpens x₀ y₀) m ?_ ?_ ?_
  · refine T.homeo _ _ (interOpensHomeo x₀ y₀) m ?_
    refine kY'.prod _ (dX - 1) (fun a ha => hX.puncturedVanish a (by omega)) m (by omega)
  · refine T.homeo _ _ (leftOpensHomeo x₀ y₀) (m + 1) ?_
    refine kY.prod _ (dX - 1) (fun a ha => hX.puncturedVanish a (by omega)) (m + 1) (by omega)
  · refine T.homeo _ _ (rightOpensHomeo x₀ y₀) (m + 1) ?_
    refine kY'.prod X dX hX.vanish (m + 1) (by omega)

/-- The conclusion Step C consumes: the punctured space has no cohomology in the top
degree of the unpunctured one. -/
theorem isZero_punctured_top {Z : Type} [TopologicalSpace Z] {d : ℕ} {z : Z}
    (h : PuncturedAcyclicOf K Z d z) :
    IsZero (Hmod K (TopCat.of ↥({z}ᶜ : Set Z)) d) :=
  h.puncturedVanish d le_rfl

/-- The same, as a `Subsingleton` statement, which is the form in which
`ThomFieldTwo.surjective_of_exact_of_subsingleton` takes it. -/
theorem subsingleton_punctured_top {Z : Type} [TopologicalSpace Z] {d : ℕ} {z : Z}
    (h : PuncturedAcyclicOf K Z d z) :
    Subsingleton (Hmod K (TopCat.of ↥({z}ᶜ : Set Z)) d) :=
  ModuleCat.subsingleton_of_isZero h.isZero_punctured_top

end PuncturedAcyclicOf

/-! ## The `F₂` vocabulary

Every name above is the generic one; the mod-2 spellings are reducible `abbrev`s and
`export` aliases at `K = ZMod 2`, so the verified mod-2 answer to LIX and the fourteen `LIX*`
files that name one of the three are byte-unchanged.  `K` is *implicit* in every theorem of this file because some
argument always determines it (the toolkit, the Künneth factor, or the acyclicity datum), so
no call site has to name it. -/

/-- The mod-2 cohomology toolkit: `CohomologyToolkitOf (ZMod 2)`. -/
abbrev CohomologyToolkit : Prop := CohomologyToolkitOf (ZMod 2)

/-- A mod-2 Künneth factor: `KunnethFactorOf (ZMod 2)`. -/
abbrev KunnethFactor (Y : Type) [TopologicalSpace Y] (q : ℕ) : Prop :=
  KunnethFactorOf (ZMod 2) Y q

/-- Mod-2 top-punctured acyclicity: `PuncturedAcyclicOf (ZMod 2)`. -/
abbrev PuncturedAcyclic (Z : Type) [TopologicalSpace Z] (d : ℕ) (z : Z) : Prop :=
  PuncturedAcyclicOf (ZMod 2) Z d z

/-- **The recursion at `ZMod 2`.**  A real wrapper, not an `export` alias, and the reason is
worth stating: dot notation resolves the head constant of the type *as written*, finds
`PuncturedAcyclic.prod`, and then looks for a parameter whose type is headed by
`PuncturedAcyclic`.  An alias pointing at `PuncturedAcyclicOf.prod` has no such parameter, so
the alias BREAKS `hX.prod` — and without any alias at all, dot notation unfolds the reducible
`abbrev` and finds `PuncturedAcyclicOf.prod` by itself.  So aliases exist here only for the
names used by *qualified* spelling, and their binders are written with the `F₂` names so that
both spellings work. -/
theorem PuncturedAcyclic.prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y] (T : CohomologyToolkit) {dX dY : ℕ} {x₀ : X} {y₀ : Y}
    (kY : KunnethFactor Y dY) (kY' : KunnethFactor ↥({y₀}ᶜ : Set Y) (dY - 1))
    (hX : PuncturedAcyclic X dX x₀) (hY : PuncturedAcyclic Y dY y₀) :
    PuncturedAcyclic (X × Y) (dX + dY) (x₀, y₀) :=
  PuncturedAcyclicOf.prod T kY kY' hX hY

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if it
leaves the classical allowlist, which `#print axioms` does not.  The recursion is the whole
content of this file, and it is now generic in `K`. -/

#audit_axioms PuncturedAcyclicOf.prod

end GroupApproximation.CharClass
