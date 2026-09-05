# cc-cohom-api

Lane of `notes/LIX_FULL_PROGRAM_2026-09-05.md`.  Owns
`GroupApproximation/CharClass/Cohomology*.lean`, namespace
`GroupApproximation.CharClass`.

Everything is the **vendored** mod-2 singular cohomology
(`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`),
repackaged element-wise.  Spaces are `TopCat.{0}`; `Hmod2 X n` is a
`ModuleCat (ZMod 2)` and is *reducibly* the vendored `cohomologyZMod2 X n`, so a
peer may mix the two vocabularies freely.

## Module map

| module | contents |
|---|---|
| `CohomologyBasic.lean` | `Hmod2`, `cohCast`, `cup` (`⌣`), `one`, `pull`, bilinearity, right unitality, naturality, functoriality |
| `CohomologyAssoc.lean` | degree relabelling of simplices, `cochainCup_assoc`, `cup_assoc`, `one_cup` |
| `CohomologyBridge.lean` | `TopCat.of` plumbing for concrete `Type`s, subspace restriction, products, homotopy invariance, `H^*(X × [0,1])`, `H^*(X × ℝ^k)` |
| `CohomologySphere.lean` | `H^k(S^n; F₂)` (planned) |
| `CohomologyMayerVietoris.lean` | element-form Mayer–Vietoris (planned) |
| `CohomologyKunneth.lean` | Künneth with spheres (planned) |

## Exported signatures (stable; build against these)

```lean
namespace GroupApproximation.CharClass

abbrev Hmod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2)   -- = cohomologyZMod2 X n

def cohCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod2 X m) : Hmod2 X m'
def cup {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) : Hmod2 X (p + q)
scoped infixl:70 " ⌣ " => cup
def one (X : TopCat.{0}) : Hmod2 X 0
def pull {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod2 Y n) : Hmod2 X n
def pullLinear {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : Hmod2 Y n →ₗ[ZMod 2] Hmod2 X n
def cupBilin (X : TopCat.{0}) (p q : ℕ) :
    Hmod2 X p →ₗ[ZMod 2] Hmod2 X q →ₗ[ZMod 2] Hmod2 X (p + q)

theorem cup_mk       -- class of a cocycle ⌣ class of a cocycle = class of cochainCup
theorem cup_add_left / cup_add_right / cup_smul_left / cup_smul_right / zero_cup / cup_zero
theorem cup_one (a : Hmod2 X p) : cup a (one X) = a            -- STRICT, no cast
theorem one_cup (a : Hmod2 X p) : cup (one X) a = cohCast (Nat.zero_add p).symm a
theorem cup_assoc (a b c) :
    cup (cup a b) c = cohCast (Nat.add_assoc p q r).symm (cup a (cup b c))
theorem pull_id / pull_comp / pull_add / pull_zero / pull_smul / pull_congr / pull_mk
theorem pull_cup (f) (a b) : pull f (p+q) (cup a b) = cup (pull f p a) (pull f q b)
theorem pull_one (f) : pull f 0 (one Y) = one X

-- bridge
abbrev cmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    TopCat.of X ⟶ TopCat.of Y
def pullMap (f : C(X, Y)) (n : ℕ) : Hmod2 (TopCat.of Y) n → Hmod2 (TopCat.of X) n
theorem pull_eq_of_homotopic / pull_eq_of_homotopy / pullMap_eq_of_homotopic
def pullEquivOfHomotopyEquiv (e : X ≃ₕ Y) (n) : Hmod2 (of Y) n ≃ₗ[ZMod 2] Hmod2 (of X) n
def pullEquivOfHomeomorph (e : X ≃ₜ Y) (n) : Hmod2 (of Y) n ≃ₗ[ZMod 2] Hmod2 (of X) n
def pullEquivOfIso {X Y : TopCat.{0}} (e : X ≅ Y) (n) : Hmod2 Y n ≃ₗ[ZMod 2] Hmod2 X n
def inclSubtype (S : Set X) : TopCat.of S ⟶ TopCat.of X
def restrictTo (S : Set X) (n) : Hmod2 (of X) n → Hmod2 (of S) n
abbrev fstMap / sndMap / prodMap
def cohProdContractible (X C) [ContractibleSpace C] (n) :
    Hmod2 (of X) n ≃ₗ[ZMod 2] Hmod2 (of (X × C)) n            -- = pull (fstMap X C) n
def cohProdUnitInterval (X) (n) / cohProdEuclidean (X) (k n)

end GroupApproximation.CharClass
```

## 1. GREEN

*(nothing yet — first probe of `CohomologyBasic` in flight)*

## 2. AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/CohomologyBasic.lean`
* `GroupApproximation/CharClass/CohomologyAssoc.lean`
* `GroupApproximation/CharClass/CohomologyBridge.lean`

## 3. NEEDS

* **`cc-cartan`: graded commutativity.**  The vendored Alexander–Whitney cup
  product is not commutative on the nose and the vendored tree has **no** chain
  homotopy between the AW diagonal and its transpose, so
  `cup a b = cohCast (Nat.add_comm p q) (cup b a)` is **not** provided by this
  lane.  It needs the ℤ/2-equivariant acyclic-models theorem.  Until it lands,
  state downstream lemmas for classes pulled back from *different* factors of a
  product, where the commutation follows from naturality alone.
  Signature wanted:

  ```lean
  theorem cup_comm {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
      cup a b = cohCast (Nat.add_comm q p) (cup b a)
  ```

## 4. TRAPS

* The vendored `CohomologyCupProduct.lean` **already** carries the cohomology-level
  product `cupZMod2`, the unit `oneZMod2`, `cupZMod2_mk`, `cohPullback` and
  `cohPullback_cupZMod2`.  Do not re-derive the descent; only bilinearity,
  associativity and unitality were missing.
* The vendored **Mayer–Vietoris is homological** (`mvShortExact`, `mvHomologyIso`
  over `ChainComplex (ModuleCat R) ℕ`), not cohomological.  A cohomology
  Mayer–Vietoris has to be built either by dualizing the degreewise-split short
  exact sequence of chain complexes, or through the vendored universal
  coefficient isomorphism `kroneckerEquiv X n : H^n(X;F₂) ≅ (H_n(X;F₂))^*`
  (`KroneckerNaturality.lean`) — but the UCT route does **not** deliver the
  `H^*(X)`-linearity of the connecting map, which is a cochain-level statement.
* `p + 0` reduces to `p` but `0 + p` does not, and `p + q + r` is not
  definitionally `p + (q + r)`.  Right unitality is therefore free and left
  unitality and associativity need `cohCast`.
