# cc-projective — `H^*(ℂP^n)`, Leray–Hirsch, mod-2 Chern classes

Owns `GroupApproximation/CharClass/{ProjectiveSpace*,LerayHirsch*,Chern*}.lean`,
namespace `GroupApproximation.CharClass`.  Deliverables: §1.4 items 1–4 of
`notes/LIX_FULL_PROGRAM_2026-09-05.md`.

## Design in one paragraph

Chern classes are defined by a polynomial relation, so they need a **ring**.
The ring is `EvenH X := ⨁_n H^{2n}(X;F₂)`: restricting to even degrees is what
kills the Koszul signs, and nothing is lost because Leray–Hirsch splits the even
part of `H^*(P(E))` freely over the even part of `H^*(X)` on `1, ξ, …, ξ^{r-1}`,
while every `γ_i(E) ∈ H^{2i}(X)` is even by construction.  A Leray–Hirsch
conclusion **is** a Mathlib `PowerBasis (EvenH X) (EvenH (P E))`, and the Chern
polynomial **is** its `minpolyGen`; uniqueness of a monic annihilator of the right
degree then yields naturality, the split form `γ_k = e_k(y)`, and Whitney along
an injective base change, with no further topology.  The topological inputs enter
as `structure`s in element form (`MVSequence`, `GysinSequence`), so every theorem
below is proved *now*, about any space carrying one, and instantiating them is
the only thing that waits on peers.

## Module map

| module | content | needs |
|---|---|---|
| `ChernRelation.lean` | `chernPoly` = `PowerBasis.minpolyGen`; uniqueness; `chernClass`; rank bound; naturality; split case `γ_k = e_k(y)`; Whitney via an injective base change | Mathlib only |
| `LerayHirschAlgebra.lean` | five lemma in element form (Mathlib has none at this pin); `powerBasisOfBijective` | Mathlib only |
| `ProjectiveSpace{Basic,Chart,Hyperplane,Puncture,Retract,TwoCover,Sphere}.lean` | the point-set chain over `CP d`: chart `ℂ^d ≃ chartSet`, hyperplane `ℂP^d ↪ ℂP^{d+1}`, `rad`, the scaling deformation, `ℂP^{d+1}∖pt ≃ ℂP^d`, `chartSet ∩ punctured ≃ S^{2d+1}`, `ℂP^0 = pt` | `Analysis/LIXProjectiveSpaceModel` |
| `ProjectiveSpaceCover.lean` | that cover as two `Opens` of a `TopCat.{0}` object | above |
| `ProjectiveSpaceCohomology.lean` | `MVSequence`; propagate / create / vanish; `HasPointCohomology`, `HasSphereCohomology`, `HasCPCohomology`; the inductive step `hasCPCohomology_succ` | `CohomologyBasic` |
| `ProjectiveSpaceRing.lean` | `lineGen` (an `F₂`-line has a *unique* nonzero element); `cupPowE`; `GysinSequence`; `bijective_cupRight`; `cupPowE_ne_zero`; `h^{N+1} = 0` | above |
| `ChernEuler.lean` | `eulerClass hgen f = f^* h`; naturality; vanishing on a factored map; stability of the generator along `ℂP^d ⊆ ℂP^{d+1}` | above |
| `ChernEvenPiece.lean` | `EvenPiece`, `evenMul`, `evenOne`, distributivity, right unitality, `pullEven`; `EvenH` as an additive group with `of`/`component` | `CohomologyBasic` |
| `ChernEvenRing.lean` | left unitality, associativity, `evenGRing` | + `cup_assoc`, `one_cup` |
| `ChernEvenRingComm.lean` | `evenMul_comm`, the `GCommRing` instance, `EvenH.map` as a `RingHom` | + `cup_comm` |

## 1. GREEN

| module | jobs |
|---|---|
| `CharClass/LerayHirschAlgebra.lean` | 8679 (`✔ [8668/8679] Built … (42s)`) |
| `CharClass/ProjectiveSpaceBasic.lean` | 8677 (`✔ [8670/8677] Built … (124s)`) |

## 2. AUTHORED, UNVERIFIED

`ChernRelation`, `ProjectiveSpaceCohomology`, `ProjectiveSpaceRing`, `ChernEuler`,
`ProjectiveSpace{Chart,Hyperplane,Puncture,Retract,TwoCover,Sphere,Cover}`,
`ChernEvenPiece`, `ChernEvenRing`, `ChernEvenRingComm` — probe in flight after the
first round of fixes.

Still to author (blocked on the two lanes below, design settled): Leray–Hirsch
for `P(L⊕1)` and in general by Mayer–Vietoris induction over a finite
trivializing cover, using `bijective_of_ladder`; the construction of the
`GysinSequence` of `S(L)` from the Mayer–Vietoris of
`P(L⊕1) = E(L) ∪ (P(L⊕1)∖Z)`; `γ_i(E)` for a projection-model bundle; Whitney and
the splitting principle via the flag bundle.

## 3. NEEDS

### From `cc-cohom-api`

1. **`cup_assoc`, `one_cup`.**  `CharClass/CohomologyAssoc.lean` currently
   contains four `sorry`s and two `expected token` parse errors (my probe,
   8670/8679) — reported to the lane.  `AlgTop/CupAssoc.lean` already has both
   at cochain level for the *vendored* `cochainCup` at general `CommRing R`
   (`cochainCup_assoc`, `cochainCup_one_left`); the descent is ten lines.
2. **`cup_comm`**, in the shape `cup a b = cohCast (Nat.add_comm q p) (cup b a)`.
   The lane has declined it and points at `cc-cartan`; I have asked
   `cc-steenrod` for it as the first corollary of the `⌣₁` coboundary formula.
   Even degrees suffice for me.  **This is the single blocking need**: without it
   `EvenH X` is a `Ring` but not a `CommRing`, and `PowerBasis` wants a
   `CommRing`.
3. **Mayer–Vietoris in element form**, to instantiate `MVSequence`
   (`CharClass/ProjectiveSpaceCohomology.lean`): four restriction maps, `δ`, and
   exactness at the three spots stated as `∀ x, g x = 0 ↔ ∃ y, f y = x`.  Plus
   the `H^*(X)`-linearity `δ (a ⌣ pull ι b) = δ a ⌣ b` for `b` global, which
   Leray–Hirsch needs and which the universal-coefficients route cannot give.
4. **`H^k(S^n;F₂)`, `H^k(pt;F₂)`**, in the shape of `HasSphereCohomology` /
   `HasPointCohomology`, and **homotopy invariance** as a `LinearEquiv`
   (`pullEquivOfHomotopyEquiv`), which is what `HasCPCohomology.of_linearEquiv`
   consumes.
5. **Künneth with spheres**, for the products in `cc-thom`'s recursion.

### From `cc-bundle`

`P(p) ⊆ X × CP(K-1)` with its tautological line; `P(p) ⊆ P(p ⊕ 1)`;
`E(p) = P(p⊕1) ∖ P(p)`; the zero section and `P(p⊕1)∖Z ≃ P(p)`; a **finite**
trivializing open cover with the local homeomorphisms `P(p)|_U ≅ U × CP^{r-1}`;
the classifying map `f_L : X → CP(K-1)` of a rank-one projection and the rotation
homotopy that makes it well defined on isomorphism classes; the flag bundle as an
iterated `P(-)`.

## 4. TRAPS

* **`scratchpad/cc/ccprobe.sh` is broken for more than one changed file.**  The
  changed-file list keeps its newlines and is spliced into a remote
  `for f in $CHANGED; do …; done`, so the remote shell dies with
  `syntax error near unexpected token` before running anything.  On the *first*
  probe after a clone is created every file counts as changed and the local
  `msi` call dies with `Argument list too long` instead.  Both exit **0**,
  because the trailing `| tail -N` masks the status, so they look like a probe
  that simply produced no `Build completed` line.  Fix: `| tr '\n' ' '` on the
  `awk` capture.  Reported to the lead; I use a fixed copy at
  `scratchpad/ccp/ccprobe_projective.sh`.
* **`AlgTop/ComplexProjective*.lean` is red and unowned.**  `ComplexProjectiveBasic`
  fails on an unused simp argument (`Pi.single_apply`), fatal under
  `-DwarningAsError=true`.  The chain is re-proved in this lane's namespace
  rather than edited.  Two further breakages surfaced in the copy:
  `rw [normalize]` unfolds only the first of two occurrences (use two `have`s,
  one of them `rfl`), and `rw [… , sq]` normalises only the numerator of
  `‖·‖²/r²` (finish with `ring`).
* **`Polynomial.natDegree_prod` needs `NoZeroDivisors`.**  For a product of monic
  polynomials use `natDegree_prod_of_monic`, which does not.
* **`Polynomial.finset_sum_coeff` is deprecated** at this pin; deprecation is an
  error.  Use `finsetSum_coeff`.
* **`PowerBasis.degree_minpolyGen` needs `[Nontrivial A]`** on the *source* ring,
  so `chernPoly_map` needs it on both sides, not just the target.
* **A section `variable (mv : …)` is not in scope in a theorem whose statement
  does not mention it**, and field notation `mv.foo` then fails with
  `Unknown identifier`.  Make the structure argument explicit.
* **`Nat.mul` recurses on its second argument**, so `2 * 0` reduces to `0` and
  `2 * (m+1)` reduces to `2*m + 2`, definitionally.  Cup powers of a degree-two
  class therefore need *no* degree transport, and `evenOne` needs none either.
  `0 + p` does **not** reduce to `p`, which is why left unitality does need one.
* **`LinearMap.mk … map_smul_of_tower` does not find `CompatibleSMul _ _ (ZMod 2) ℤ`.**
  Over `F₂` every additive map is linear for a one-line reason (`∀ z : ZMod 2,
  z = 0 ∨ z = 1` by `decide`); `toLinearZMod2` in
  `CharClass/ProjectiveSpaceCohomology.lean` packages it.
* **An `F₂`-line has a unique nonzero element**, so "the" degree-2 generator of
  `H^*(ℂP^n)` needs no orientation choice at all — `lineGen`, with `lineGen_eq`
  saying any two constructions agree.  This is the main way the mod-2 theory is
  cheaper than the integral one here.
