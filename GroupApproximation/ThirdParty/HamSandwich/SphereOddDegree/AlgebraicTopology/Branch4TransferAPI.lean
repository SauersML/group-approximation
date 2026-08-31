import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferAssembly
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNonzero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferHomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2

/-!
# Branch 4 — Normalized transfer API and notation (Prompt 52)

This file is a small **API-normalization layer** for Branch 4. It introduces no
new mathematical content: every declaration is either

* an `abbrev`/`def` alias of an existing project declaration (in *exactly* its
  existing type), or
* a short restatement of an existing theorem.

Its purpose is that later prompts can `import` this single file and use short,
stable `b4_`-prefixed names without searching through the older transfer files or
depending on unstable long names.

The canonical existing declarations wrapped here (see `Branch4TransferInventory.md`
from Prompt 51) are:

* homology transfer `Hₖ(RPⁿ; F₂) ⟶ Hₖ(Sⁿ; F₂)` — `projTransferHomologyZMod2`;
* cohomology transfer `Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂)` — `cohTransferZMod2`;
* the Kronecker/evaluation pairing — `kroneckerMap`;
* the transfer–Kronecker adjunction — `cohTransferZMod2_kronecker_adjunction`;
* the actual RPⁿ top cohomology class `αⁿ` — `rpTopClass`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## Spaces

Canonical aliases for the two spaces. These alias the *existing* project spaces
`Sphere` and `RP`; no new spaces are created. -/

/-- Canonical Branch-4 name for the sphere `Sⁿ` (alias of `Sphere`). -/
abbrev B4Sphere (n : ℕ) := Sphere n

/-- Canonical Branch-4 name for real projective space `RPⁿ` (alias of `RP`). -/
abbrev B4RP (n : ℕ) := RP n

/-! ## Homology and cohomology objects

Canonical aliases for the mod-2 (co)homology `ModuleCat (ZMod 2)`-objects, in
their existing types. The homology objects use `homologyZMod2` (the type in which
the Kronecker classifier and the adjunction are stated); this is definitionally
the same object as `singularHomologyCxZMod2` used by the homology transfer. -/

/-- `Hₖ(Sⁿ; F₂)` as a `ModuleCat (ZMod 2)`-object. -/
abbrev b4_sphereHomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (Sphere n)) k

/-- `Hₖ(RPⁿ; F₂)` as a `ModuleCat (ZMod 2)`-object. -/
abbrev b4_rpHomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (RP n)) k

/-- `Hᵏ(Sⁿ; F₂)` as a `ModuleCat (ZMod 2)`-object (alias of `sphereCohomology`). -/
abbrev b4_sphereCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  sphereCohomology n k

/-- `Hᵏ(RPⁿ; F₂)` as a `ModuleCat (ZMod 2)`-object (alias of `rpCohomology`). -/
abbrev b4_rpCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  rpCohomology n k

/-! ## Homology transfer `RPⁿ → Sⁿ`

The existing transfer is a `ModuleCat (ZMod 2)` morphism (a chain-map-induced
homology map), not a bare `LinearMap`; we alias it in that exact type. -/

/-- Canonical Branch-4 name for the mod-2 homology transfer
`Hₖ(RPⁿ; F₂) ⟶ Hₖ(Sⁿ; F₂)` of the double cover (alias of
`projTransferHomologyZMod2`). -/
def b4_transferHomologyRPToSphere (n k : ℕ) :
    b4_rpHomology n k ⟶ b4_sphereHomology n k :=
  projTransferHomologyZMod2 n k

/-! ## Cohomology transfer `Sⁿ → RPⁿ`

Likewise a `ModuleCat (ZMod 2)` morphism, aliased in its exact type. -/

/-- Canonical Branch-4 name for the mod-2 cohomology transfer
`Hᵏ(Sⁿ; F₂) ⟶ Hᵏ(RPⁿ; F₂)` of the double cover (alias of `cohTransferZMod2`). -/
def b4_cohTransferSphereToRP (n k : ℕ) :
    b4_sphereCohomology n k ⟶ b4_rpCohomology n k :=
  cohTransferZMod2 n k

/-! ## Kronecker pairing

Canonical names for the mod-2 Kronecker (evaluation) pairing
`⟨-,-⟩ : Hᵏ(X; F₂) × Hₖ(X; F₂) → F₂`, obtained from the classifier
`kroneckerMap`. -/

/-- The Kronecker pairing `⟨c, x⟩` on `RPⁿ` in degree `k`. -/
def b4_pairingRP (n k : ℕ) (c : b4_rpCohomology n k) (x : b4_rpHomology n k) : ZMod 2 :=
  (kroneckerMap (TopCat.of (RP n)) k).hom c x

/-- The Kronecker pairing `⟨c, z⟩` on `Sⁿ` in degree `k`. -/
def b4_pairingSphere (n k : ℕ) (c : b4_sphereCohomology n k) (z : b4_sphereHomology n k) : ZMod 2 :=
  (kroneckerMap (TopCat.of (Sphere n)) k).hom c z

/-! ## Top classes and generators

We alias only the classes that exist as project data.

* The **RPⁿ top cohomology class** `αⁿ` exists as `rpTopClass n m`, parameterized
  by a `MonodromyFunctional n` (the datum from which the degree-one class
  `rpAlpha` is built); we alias it preserving that parameter. -/

/-- Canonical Branch-4 name for the RPⁿ top cohomology class `αⁿ ∈ Hⁿ(RPⁿ; F₂)`,
parameterized by the monodromy functional `m` (alias of `rpTopClass`). -/
def b4_rpTopClass (n : ℕ) (m : MonodromyFunctional n) : b4_rpCohomology n n :=
  rpTopClass n m

/-- The Branch-4 RPⁿ top class is the `n`-th cup power of `rpAlpha` (restatement of
`rpTopClass_eq_rpAlpha_power`). -/
theorem b4_rpTopClass_eq_rpAlpha_power (n : ℕ) (m : MonodromyFunctional n) :
    b4_rpTopClass n m = cupPowZMod2 (rpAlpha n m) n :=
  rpTopClass_eq_rpAlpha_power n m

/-
Missing project data (recorded here for later prompts; not faked):

-- Missing top-(co)homology generators for later prompts:
--   b4_sphereTopHomologyGenerator (n : ℕ) : b4_sphereHomology n n
--   b4_rpTopHomologyGenerator     (n : ℕ) : b4_rpHomology n n
--   b4_sphereTopClass             (n : ℕ) : b4_sphereCohomology n n
-- The project pins no named constant for the sphere/RPⁿ top *homology* generators,
-- nor for the sphere top *cohomology* class: the homology side is handled
-- abstractly through `b4_sphereHomology`/`b4_rpHomology` (elements `z`/`x`), and
-- the sphere top cohomology class is used abstractly as `c : b4_sphereCohomology n n`
-- with `c ≠ 0`.  Do not invent this data.
-/

/-! ## Canonical theorem restatements -/

/-- **Transfer–Kronecker compatibility** (restatement of
`cohTransferZMod2_kronecker_adjunction`, available in top degree `k = n`):
pairing the cohomology transfer of `c` against an RPⁿ class `x` equals pairing
`c` against the homology transfer of `x`,
`⟨tr c, x⟩_{RPⁿ} = ⟨c, tr_* x⟩_{Sⁿ}`. -/
theorem b4_cohTransfer_kronecker
    (n : ℕ)
    (c : b4_sphereCohomology n n)
    (x : b4_rpHomology n n) :
    b4_pairingRP n n ((b4_cohTransferSphereToRP n n).hom c) x
      = b4_pairingSphere n n c ((b4_transferHomologyRPToSphere n n).hom x) :=
  cohTransferZMod2_kronecker_adjunction n c x

/-
### One-dimensional top cohomology uniqueness

The project does **not** currently contain a `pairing-against-a-fixed-generator`
uniqueness theorem for `Hⁿ(RPⁿ; F₂)` (there is no named RPⁿ top *homology*
generator to pair against; see the "missing data" note above), so it is not
restated here.  What *is* available from the additive computation is the
rank-one/spanning fact, restated next.

-- Missing theorem for a later prompt (do not fake):
-- b4_rpTopCohomology_eq_of_pairing_generator
--   (n : ℕ) (c : b4_rpCohomology n n)
--   (hpair : b4_pairingRP n n c (b4_rpTopHomologyGenerator n) = 1) :
--   c = b4_rpTopClass n
-/

/-- **One-dimensionality of top RPⁿ cohomology** (restatement of
`rpCohomology_rank_one` at `k = n`): given the cellular datum `cc`, the top group
`Hⁿ(RPⁿ; F₂)` has `F₂`-dimension one. This is the rank-one/spanning form of the
top-cohomology uniqueness statement. -/
theorem b4_rpTopCohomology_finrank_one (n : ℕ) (cc : RPnCellularCochainStructure n) :
    Module.finrank (ZMod 2) (b4_rpCohomology n n) = 1 :=
  rpCohomology_rank_one cc n (le_refl n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

