import GroupApproximation.Computability.BooneGroupFreeBasis
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The base group of the Aanderaa--Cohen construction, and Simpson's Lemma 5

Third module of the Novikov--Boone chain; see
`GroupApproximation.Computability.BooneGroupModularMachine` for the route, the
source, and the manuscript anchors.  The route is the modular-machine proof of
Aanderaa--Cohen 1980 as written out in

> Stephen G. Simpson, *A Slick Proof of the Unsolvability of the Word Problem
> for Finitely Presented Groups*, draft of 18 May 2005,
> `https://sgslogic.net/t20/logic/seminar/050517.pdf`

and this module is Simpson's page 2--3: the group `G = ⟨t, x, y | xy = yx⟩`, the
elements `t(α,β) = x^{-α} y^{-β} t x^{α} y^{β}`, the subgroups `T`, `T_{ab}^{MN}`
and `G_{ab}^{MN}`, the canonical isomorphism `G ≅ G_{ab}^{MN}`, and **Lemma 5**,
`T_{ab}^{MN} = T ∩ G_{ab}^{MN}`.

## The model of `G`

Simpson presents `G` by generators and relations.  Here `G` is realised as the
semidirect product

  `BaseGroup = FreeGroup (ℤ × ℤ) ⋊ Multiplicative (ℤ × ℤ)`,

the acting `ℤ²` translating the free basis.  This is the same group: `G` is
`⟨t⟩ ∗ ℤ²`, the normal closure of `⟨t⟩` in it is free on the conjugates
`t(α,β)` indexed by the coset representatives `x^α y^β`, and `ℤ² = ⟨x,y⟩` splits
the quotient.  Taking the split extension as the *definition* makes the two
facts that carry the whole argument --- that `T` is free on `{t(α,β)}` and that
`T ∩ G_{ab}^{MN} = T_{ab}^{MN}` --- structural rather than an application of the
Kurosh subgroup theorem, which is not in Mathlib.  The cost is deferred:
`BaseGroup` has to be *proved* isomorphic to the two-generator-one-relator
presentation before the final group can be called finitely presented.  That is
item **S2c** of the roadmap below and it is not done here.

Under this model, with `t(α,β) = inl (of (α,β))` and `x^u y^v = inr (ofAdd
(u,v))`, the defining relations come out as Simpson has them:

* `xy = yx`, because the acting group is `ℤ²` (`sh_comm`);
* `x^{-1} t(α,β) x = t(α+1, β)` and `y^{-1} t(α,β) y = t(α, β+1)`, because the
  action is translation (`sh_conj_tw`);
* `t = t(0,0)` (`tGen`, definitionally).

## Roadmap for the rest of Novikov--Boone

Stage by stage, with the Britton applications marked.  `DONE` means "in this
repository, fully proved with no gaps"; every size is new Lean lines.

* **S0 `DONE`** (`BooneGroupModularMachine`).  Simpson's Definition 3 and
  Theorem 4's object; the three machine facts the group needs.
* **S1 `DONE`** (`BooneGroupFreeBasis`).  Sub-basis subgroups of a free group:
  `of_mem_basisSubgroup_iff`, `basisSubgroup_inf`, `map_basisSubgroup`,
  `range_indexMap`.  Nothing in it is specific to Novikov--Boone.
* **S2 `DONE`** (this file).  The base group, `t(α,β)`, `T`, `T_S`, the
  canonical embedding `G ≅ G_{ab}^{MN}` and **Simpson's Lemma 5**.
* **S2b `DONE`** (this file, `Gsub_eq_closure`).  The reverse inclusion of `closure_le_Gsub`, i.e.
  `G_{ab}^{MN} = ⟨t(a,b), x^M, y^N⟩` --- that the range of `emb` is Simpson's
  *definition* of `G_{ab}^{MN}`.  Route, with all Mathlib ingredients checked
  present at the pinned revision: `Gsub = (⊤).map emb` by
  `MonoidHom.range_eq_map`; `⊤ = Subgroup.closure {t, x, y}` from
  `sh_conj_tw` (which writes `t(p) = x^{-p} t x^{p}`),
  `SemidirectProduct.inl_left_mul_inr_right`, and `FreeGroup.induction_on`;
  then `Subgroup.map_closure` plus `Set.image_insert_eq` / `Set.image_singleton`
  and `emb_tGen` / `emb_sh`.  The one step to check first is `sh h ^ n =
  sh (n • h)` (via `map_zpow` and `ofAdd_zsmul`) together with the componentwise
  description of `n • (h : ℤ × ℤ)`, which is the only place the `Prod` `zsmul`
  instance is touched.
* **S2c `DONE`** (`BooneGroupPresentation`, `presentedEquiv`).
  `BaseGroup ≃* PresentedGroup ⟨t,x,y | [x,y]⟩`.
  Forward map by `PresentedGroup.toGroup`; backward by
  `SemidirectProduct.lift`; mutual inverses checked on generators.  Needed
  *only* to call the final group finitely presented.
* **S3 `DONE`** (`BooneGroupTower`), construction and per-machine assembly
  both.  Built: `Stage` (carrier + group + `ι` + injectivity as
  a bundle, which is what avoids defining a type, its instance and `ι` by one
  mutual recursion), `Stage.step`, `tower` as a fold, `tower_ι_injective`, and
  `quadEquiv`/`quadIdentification` --- the transport of
  `(emb a b M M)⁻¹ ∘ (emb c 0 M² 1)`, which is `φₙ`.  The assembly this entry
  once listed as missing is `residuePairs`, `machineIdentifications` and
  `machineTower`, with `machineTower_ι_injective`: one identification per
  residue pair carrying a quadruple, over a list rather than a `Fintype` index.
  Original entry follows.
  The tower of Simpson's Definition 6.
  Mathlib's `HNNExtension` carries one stable letter, so `G'_M` must be built
  as an iterated single-letter HNN indexed by `Fin M × Fin M` --- one stable
  letter per residue pair.  Residue pairs carrying no quadruple get `⊥` as both
  associated subgroups, which is harmless (an HNN extension with trivial
  associated subgroups is a free product with `ℤ`) and keeps the index type a
  clean `Fintype`.  Deliverables: the recursive tower `G₀ = G`,
  `G_{n+1} = HNNExtension G_n Aₙ Bₙ φₙ`; the composite `ιₙ : G →* Gₙ` and its
  injectivity from `HNNExtension.of_injective`; and `Aₙ`, `Bₙ` as the images
  under `ιₙ` of `G_{a b}^{MM}` and `G_{c 0}^{M²,1}`, with `φₙ` the transport of
  `(emb a b M M)⁻¹ ∘ (emb c 0 M² 1)`.
* **S4 `DONE`** (`BooneGroupTower`, `liftedSubgroup_inf_range`).  Proved without
  the induction this entry anticipated: put `A₁ := Asub.subgroupOf A`, so that
  for a letter *of `A`*, lying in `A₁` is the same as lying in `Asub`; then a
  reduced word over `A` pushes forward to a reduced word over `G` (`pushWord`,
  whose `chain` field transfers letter by letter), and Britton applies directly
  in the big extension.  No pinching, no induction on the number of stable
  letters.  Original entry follows.
  Simpson's Definition 2, the
  *good subgroup* lemma: if `A ≤ G` satisfies `φ(A ⊓ Asub) = A ⊓ Bsub`, then
  `A' ⊓ of.range = A.map of`, where `A'` is generated by `of '' A` and `t`.
  This is the only place Britton's Lemma is used.  Mathlib's
  `Mathlib/GroupTheory/HNNExtension.lean` supplies everything needed for the
  single-stable-letter case, at the pinned revision:
  `NormalWord` *extends* `NormalWord.ReducedWord`; `NormalWord.prod_smul` and
  `prod_empty` give `(g • empty).prod φ = g`, so every element has a reduced
  spelling with no extra work; `ReducedWord.exists_normalWord_prod_eq`,
  `ReducedWord.map_fst_eq_and_of_prod_eq`, `NormalWord.prod_injective`,
  `equiv`, `of_injective`, and Britton itself
  (`ReducedWord.toList_eq_nil_of_mem_of_range`) are all present.  The remaining
  work is the induction: turn an arbitrary word `a₀ t^{ε₁} a₁ ⋯ t^{εₙ} aₙ` with
  `aᵢ ∈ A` into a reduced one, pinching with `φ` and using goodness to stay
  inside `A`, by strong induction on `n`; then iterate up the tower of S3, each
  stage's conclusion feeding the next stage's goodness hypothesis.  The genuine
  gap is that Mathlib's HNN extension carries **one** stable letter, so the
  multi-letter statement has to be assembled stage by stage.
* **S5a `DONE`** (`BooneGroupMachineIndex`).  The *base-group half* of both
  good-subgroup verifications, for an arbitrary modular machine and with no HNN
  theory: `T ⊓ G_{ab}^{MN}` and `T_M ⊓ G_{ab}^{MN}` are computed
  (`Tsub_inf_Gsub_image`, `twSub_halting_inf_Gsub`), and the source and target
  sides at a quadruple are exhibited as the two images of **one and the same**
  parameter set (`twSub_halting_inf_Gsub_src` versus
  `twSub_halting_inf_Gsub_right` / `_left`).  That is the good-subgroup
  condition with the associated isomorphism left implicit.
* **S5b `DONE`** (`BooneGroupGoodness`).  Both directions:
  `good_twSub_halting_right`/`_left` and
  `twSub_halting_liftedSubgroup_inf_right`/`_left`.  Goodness of `T_M` is S5a's
  two computations read through `twSub_map_emb`, and S4 then applies with nothing
  left to compute.  Original entry follows.
  Supply the isomorphism: feed S5a into S4 to get
  `T = T' ⊓ G` and `T_M = T'_M ⊓ G` inside the tower.  What remains is purely
  the HNN transport --- rewriting S5a's two images along
  `emb c 0 M² 1 ∘ (emb a b M M)⁻¹`, which is well defined because
  `emb_injective` holds.
* **S6 `DONE`** (`BooneGroupGoodness`, `towerSub_halting_eq_towerTSub`).  The
  displayed computation is `stable_conj_emb_right`/`_left` --- the stable letter
  carries the source embedding onto the target --- and the finished proof does
  string those steps along a halting computation: `ι_tw_mem_towerTSub_of_halts`
  runs `Relation.ReflTransGen.head_induction_on` backwards from `(0,0)`, and its
  step is `ι_tw_mem_towerTSub_of_target_right`/`_left` at the level the
  configuration's own quadruple names.  Which level that is comes from the
  division algorithm (`coe_eq_embIdx_src`, `step_right_eq_embIdx`,
  `step_left_eq_embIdx`), and that level's stable letter, mapped to the top of
  the tower, is in `⟨t⟩'` by `liftUp_t_mem_towerTSub` --- so no stable letter is
  ever named individually.  The two *outer* inclusions are then structural
  inductions over the identification list (`towerSub_le_of_mem` with
  `twSub_halting_le_comap` one way, `towerTSub_le_towerSub_halting` with
  `hasLetters_towerTSub` the other), which is the shape `towerSub_inf_range`
  already used one level down.  `towerSub_le_of_mem` is what replaces
  monotonicity: the hard inclusion is *false* level by level --- at the bottom
  it would ask for `T_M ≤ ⟨t⟩` --- and what is true instead is that a lift is
  generated by the base subgroup together with the stable letters.  Original
  entry follows.
  Simpson's Lemma 7, `T'_M = ⟨t⟩'`.  Induction on
  the length of the halting computation, via
  `Relation.ReflTransGen.head_induction_on`; the inductive step is the displayed
  computation `rᵢ⁻¹ t(α,β) rᵢ = t(α₁,β₁)`, which at the level of basis indices
  is `haltsZ_right_iff` again.
* **S7 `DONE` for its Britton core** (`BooneGroupTower`, `conj_t_eq_iff`):
  adjoining `k` with both associated subgroups `A` and the identity
  identification, conjugation by `k` fixes exactly the image of `A`.  The
  nontrivial direction is Britton for a single stable letter and a word of
  length two --- the chain condition of `t⁻¹ g t` is exactly `g ∈ A → -1 = 1`,
  so the word is reduced when `g ∉ A`, and Britton then says it has no stable
  letters, which is false.  **S7 itself is now `DONE`**
  (`BooneGroupGoodness`, `conj_k_finalTw_eq_iff`): `FinalGroup` adjoins `k` over
  `towerTSub`, `goodTower_machine` discharges S4's hypothesis for an actual
  machine's identification list, and the biconditional
  `k⁻¹ t(α,β) k = t(α,β) ↔ M.Halts (α,β)` follows from `conj_t_eq_iff` and S6.
  Original entry follows.
  Simpson's Theorem 8.  Adjoin `k` with
  `A = B = ⟨t⟩'` and `φ = id`; then `k⁻¹ g k = g ↔ g ∈ ⟨t⟩'` --- the nontrivial
  direction is Britton for a *single* stable letter and a length-one word,
  which **is** within reach of Mathlib's exported form.  Combine with S5, S6 and
  `of_mem_basisSubgroup_iff` to get `(α,β) ∈ H_M ↔ ⁅k, t(α,β)⁆ = 1`, then feed
  `Mathlib/Computability/Reduce.lean` to transport non-computability.
* **S8 `DONE`** (`BooneGroupFinitePresentation`, `finalGroup_isFinitelyPresented`),
  in about 300 lines rather than the 500--900 estimated here, because the
  permanence statement turned out not to need Britton's Lemma at all.
  `Algebra/HNNFinitePresentation.isFinitelyPresented_hnnExtension` is "an HNN
  extension of a finitely presented group along finitely generated associated
  subgroups is finitely presented" --- still absent from Mathlib, but Mathlib
  *defines* `HNNExtension` as a quotient of `G ∗ ℤ` and closes finite
  presentability under free products and under quotients by finitely normally
  generated subgroups, so the only content is replacing the relation family
  `{t a t⁻¹ (φ a)⁻¹ : a ∈ A}` by the relators of a generating set --- an
  equalizer argument on two homomorphisms out of `A`.  Then S2c makes the base
  presented, `Gsub_fg` makes each `G_{ab}^{MN}` three-generated, and
  `towerTSub_fg` makes `⟨t⟩'` finitely generated in the tower (it is free of
  infinite rank in the base group; what saves it is that
  `liftedSubgroup φ A = ⟨of '' A, t⟩`, so a stage costs exactly one generator).
  Original entry follows.
  Finite presentability of the final group.
  Needs S2c, plus "an HNN extension of a finitely presented group along
  finitely generated associated subgroups is finitely presented", which is not
  in Mathlib in any form, plus finite generation of `⟨t⟩'`.
* **S9 `DONE`** (`Computability.ModularMachineUndecidable`,
  `exists_modularMachine_halting_not_computablePred`).  Simpson's Theorem 4:
  some modular machine has non-computable halting set.  This was the one input
  Simpson leaves to the reader, and it is no longer a debt.
  * `Computability.QuadMachine` reads a modular machine as what it is: a machine
    on two stacks of base-`m` digits, since a step pops the last digit of each of
    `α`, `β` and pushes two onto one of them.  `halts_encCfg_iff` is the
    equivalence between *reaching* `(0,0)` and the two-stack machine running out
    of instructions.  Reaching `(0,0)` forces an erasure, and erasing needs to
    know when a stack is empty, which is why digit `0` is reserved for "past the
    end" and symbols start at `1`: then `halts_transfer`/`halts_drain` empty both
    stacks with four quadruples and no end markers.
  * `Computability.QuadMachineTM0` puts a `Turing.TM0` machine on those stacks.
    A `TM0` write does not move and a two-stack step always does, so a write is
    two steps --- off the cell and back, `Tape.move_left_right` --- and the
    orientation of the head, carried in the configuration and in the state,
    flips whenever the head turns around.  `QHalts_iff_TMHalts` is the
    simulation; `TM0Restrict` first cuts the machine down to the finite state
    set `TM0.Supports` provides, because the compiler's state type carries no
    `Fintype` instance and a two-stack machine has to number its states.
  * `Computability.UniversalMachineUndecidable` supplies the `TM0` machine, from
    Mathlib's `ComputablePred.halting_problem` through Mathlib's `PartrecToTM2`.
  The old entry read as follows.
  It is deliberately **not stated in Lean
  anywhere** in this chain --- not as a hypothesis, not as a named predicate.
  See the corresponding section of
  `GroupApproximation.Computability.BooneGroupModularMachine` for the debt in
  prose.  Nothing below S9 depends on it: S3--S7 produce the *biconditional*
  correctness statement for an **arbitrary** modular machine, which is the whole
  mathematical content of Novikov--Boone; the undecidability capstone is a
  two-line corollary that must be written only once Theorem 4 is proved.

**The target statement, and it is proved.**  Everything above converges on one
unconditional theorem, which S3--S7 produce and which mentions no
undecidability whatsoever:

    for every `M : ModularMachine` and every `(α, β) : ℕ × ℕ`,
      `⁅k, t(α,β)⁆ = 1`  in  `G_M`   ↔   `M.Halts (α, β)`.

That is `BooneGroupGoodness.conj_k_finalTw_eq_iff`.  It is the whole
mathematical content of Novikov--Boone, and it carries no hypothesis on the
machine.

**Nothing remains.**  S8 and S9 both closed on 2026-08-16, and the capstone is
`Computability.NovikovBoone.exists_finitelyPresented_wordProblem_not_computablePred`:
a finitely presented group and a sequence of words in it for which triviality is
not decidable, with no hypothesis and no literature input.  It is the
conjunction of S7's biconditional, S8's finite presentation and S9's machine,
all three about the same group `G_M`.

The discipline of not naming Simpson's Theorem 4 anywhere in Lean until it was
proved paid for itself: nothing below S9 ever depended on it, so when it arrived
no statement had to be weakened, and the capstone really was two lines.
-/

namespace GroupApproximation
namespace BooneGroup
namespace Base

open FreeBasis

/-! ## The translation action of `ℤ²` on the free basis -/

/-- Translation of the free-basis index set `ℤ × ℤ`.  The sign is chosen so
that `x^{-1} t(α,β) x = t(α+1, β)`, as in Simpson. -/
def shiftIdx (h p : ℤ × ℤ) : ℤ × ℤ := p - h

theorem shiftIdx_shiftIdx (h k p : ℤ × ℤ) :
    shiftIdx h (shiftIdx k p) = shiftIdx (h + k) p := by
  simp only [shiftIdx]
  abel

theorem shiftIdx_zero (p : ℤ × ℤ) : shiftIdx 0 p = p := sub_zero p

theorem shiftIdx_leftInv (h : ℤ × ℤ) :
    Function.LeftInverse (shiftIdx (-h)) (shiftIdx h) := by
  intro p
  simp only [shiftIdx]
  abel

theorem shiftIdx_rightInv (h : ℤ × ℤ) :
    Function.LeftInverse (shiftIdx h) (shiftIdx (-h)) := by
  intro p
  simp only [shiftIdx]
  abel

/-- The automorphism of `T = FreeGroup (ℤ × ℤ)` translating the basis. -/
def shiftAut (h : ℤ × ℤ) : MulAut (FreeGroup (ℤ × ℤ)) where
  toFun := fun w => indexMap (shiftIdx h) w
  invFun := fun w => indexMap (shiftIdx (-h)) w
  left_inv := indexMap_leftInverse (shiftIdx_leftInv h)
  right_inv := indexMap_leftInverse (shiftIdx_rightInv h)
  map_mul' := fun v w => map_mul (indexMap (shiftIdx h)) v w

@[simp] theorem shiftAut_apply (h : ℤ × ℤ) (w : FreeGroup (ℤ × ℤ)) :
    shiftAut h w = indexMap (shiftIdx h) w := rfl

theorem shiftAut_of (h p : ℤ × ℤ) :
    shiftAut h (FreeGroup.of p) = FreeGroup.of (p - h) := by
  rw [shiftAut_apply, indexMap_of]
  rfl

/-- The action of `ℤ²` on `T`, as a homomorphism into `MulAut T`.  The pattern
follows `GroupApproximation.lampActionHom`. -/
def shiftHom : Multiplicative (ℤ × ℤ) →* MulAut (FreeGroup (ℤ × ℤ)) where
  toFun h := shiftAut (Multiplicative.toAdd h)
  map_one' := by
    refine MulEquiv.ext fun w => ?_
    show indexMap (shiftIdx (0 : ℤ × ℤ)) w = w
    have h1 : indexMap (shiftIdx (0 : ℤ × ℤ)) w
        = indexMap (fun p : ℤ × ℤ => p) w :=
      indexMap_congr (f := shiftIdx 0) (g := fun p : ℤ × ℤ => p) shiftIdx_zero w
    rw [h1, indexMap_id]
  map_mul' := fun a b => by
    refine MulEquiv.ext fun w => ?_
    have key : indexMap (shiftIdx (Multiplicative.toAdd a))
          (indexMap (shiftIdx (Multiplicative.toAdd b)) w)
        = indexMap
            (shiftIdx (Multiplicative.toAdd a + Multiplicative.toAdd b)) w := by
      rw [indexMap_indexMap]
      exact indexMap_congr
        (fun p => shiftIdx_shiftIdx (Multiplicative.toAdd a)
          (Multiplicative.toAdd b) p) w
    exact key.symm

@[simp] theorem shiftHom_ofAdd (h : ℤ × ℤ) :
    shiftHom (Multiplicative.ofAdd h) = shiftAut h := rfl

/-! ## The base group -/

/-- **Simpson's base group** `G = ⟨t, x, y | xy = yx⟩`, realised as
`T ⋊ ℤ²` with `T` free on `ℤ × ℤ` and `ℤ²` translating the basis.  See the
module docstring for why the split extension is taken as the definition. -/
abbrev BaseGroup : Type :=
  FreeGroup (ℤ × ℤ) ⋊[shiftHom] Multiplicative (ℤ × ℤ)

/-- **Simpson's `t(α,β) = x^{-α} y^{-β} t x^{α} y^{β}`**: the basis element of
the free part indexed by `(α,β)`. -/
def tw (p : ℤ × ℤ) : BaseGroup := SemidirectProduct.inl (FreeGroup.of p)

/-- The element `x^{h.1} y^{h.2}` of the acting `ℤ²`. -/
def sh (h : ℤ × ℤ) : BaseGroup := SemidirectProduct.inr (Multiplicative.ofAdd h)

/-- Simpson's `t`. -/
def tGen : BaseGroup := tw (0, 0)

/-- Simpson's `x`. -/
def xGen : BaseGroup := sh (1, 0)

/-- Simpson's `y`. -/
def yGen : BaseGroup := sh (0, 1)

theorem sh_mul_sh (h k : ℤ × ℤ) : sh h * sh k = sh (h + k) :=
  (map_mul (SemidirectProduct.inr : Multiplicative (ℤ × ℤ) →* BaseGroup)
    (Multiplicative.ofAdd h) (Multiplicative.ofAdd k)).symm

/-- **The relation `xy = yx`.** -/
theorem sh_comm (h k : ℤ × ℤ) : sh h * sh k = sh k * sh h := by
  rw [sh_mul_sh, sh_mul_sh, add_comm h k]

theorem xGen_mul_yGen : xGen * yGen = yGen * xGen := sh_comm _ _

/-- **The relations `x^{-1} t(α,β) x = t(α+1,β)` and
`y^{-1} t(α,β) y = t(α,β+1)`**, in the uniform form
`(x^{u} y^{v}) t(α,β) (x^{u} y^{v})^{-1} = t(α-u, β-v)`. -/
theorem sh_conj_tw (h p : ℤ × ℤ) : sh h * tw p * (sh h)⁻¹ = tw (p - h) := by
  have hinv : (sh h)⁻¹
      = SemidirectProduct.inr (Multiplicative.ofAdd h)⁻¹ :=
    (map_inv (SemidirectProduct.inr : Multiplicative (ℤ × ℤ) →* BaseGroup)
      (Multiplicative.ofAdd h)).symm
  rw [hinv]
  show SemidirectProduct.inr (Multiplicative.ofAdd h) *
      SemidirectProduct.inl (FreeGroup.of p) *
      SemidirectProduct.inr (Multiplicative.ofAdd h)⁻¹ = tw (p - h)
  rw [← SemidirectProduct.inl_aut]
  show SemidirectProduct.inl (shiftAut h (FreeGroup.of p)) = tw (p - h)
  rw [shiftAut_of]
  rfl

/-! ## The subgroups `T` and `T_S` -/

/-- **Simpson's `T = ⟨t(α,β) | α,β ∈ ℤ⟩`**: the free part of the base group. -/
def Tsub : Subgroup BaseGroup :=
  (SemidirectProduct.inl : FreeGroup (ℤ × ℤ) →* BaseGroup).range

/-- The subgroup of `T` generated by the `t(α,β)` with `(α,β) ∈ S`.  Simpson's
`T_{ab}^{MN}` is this with `S` a residue class, and his `T_M` is this with
`S = H_M`. -/
def twSub (S : Set (ℤ × ℤ)) : Subgroup BaseGroup :=
  (basisSubgroup S).map (SemidirectProduct.inl : FreeGroup (ℤ × ℤ) →* BaseGroup)

/-- A base element lies in the free part exactly when its `ℤ²` component is
trivial. -/
theorem mem_Tsub_iff {g : BaseGroup} : g ∈ Tsub ↔ g.right = 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro h
    exact ⟨g.left, SemidirectProduct.ext rfl h.symm⟩

theorem twSub_le_Tsub (S : Set (ℤ × ℤ)) : twSub S ≤ Tsub := by
  intro g hg
  rw [twSub, Subgroup.mem_map] at hg
  obtain ⟨w, -, rfl⟩ := hg
  exact ⟨w, rfl⟩

/-- **Sub-basis subgroups of `T` intersect as their index sets do.**  This is
`FreeBasis.basisSubgroup_inf` pushed into the base group along the injective
`inl`, and it is what reduces the good-subgroup verification for `T_M`
(Simpson's Definition 2, applied after his Definition 6) to a statement about
index sets. -/
theorem twSub_inf (S T : Set (ℤ × ℤ)) : twSub S ⊓ twSub T = twSub (S ∩ T) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hS, hT⟩ := hg
    rw [twSub, Subgroup.mem_map] at hS
    rw [twSub, Subgroup.mem_map] at hT
    obtain ⟨w₁, hw₁, hg₁⟩ := hS
    obtain ⟨w₂, hw₂, hg₂⟩ := hT
    have hw : w₂ = w₁ :=
      SemidirectProduct.inl_injective (hg₂.trans hg₁.symm)
    rw [hw] at hw₂
    refine Subgroup.mem_map.2 ⟨w₁, ?_, hg₁⟩
    rw [← basisSubgroup_inf]
    exact Subgroup.mem_inf.2 ⟨hw₁, hw₂⟩
  · exact le_inf (Subgroup.map_mono (basisSubgroup_mono Set.inter_subset_left))
      (Subgroup.map_mono (basisSubgroup_mono Set.inter_subset_right))

/-- **`t(α,β) ∈ T_S` exactly when `(α,β) ∈ S`.**  This is the last step of
Simpson's Theorem 8, isolated. -/
theorem tw_mem_twSub_iff {S : Set (ℤ × ℤ)} {p : ℤ × ℤ} :
    tw p ∈ twSub S ↔ p ∈ S := by
  constructor
  · intro h
    rw [twSub, Subgroup.mem_map] at h
    obtain ⟨w, hw, hwp⟩ := h
    have hwof : w = FreeGroup.of p := SemidirectProduct.inl_injective hwp
    rw [hwof] at hw
    exact of_mem_basisSubgroup_iff.1 hw
  · intro h
    exact Subgroup.mem_map.2 ⟨FreeGroup.of p, of_mem_basisSubgroup h, rfl⟩

/-! ## The canonical embedding `G ≅ G_{ab}^{MN}` -/

/-- The basis-index scaling `(u,v) ↦ (a + uM, b + vN)` underlying Simpson's
canonical isomorphism `G ≅ G_{ab}^{MN}`. -/
def embIdx (a b M N : ℤ) (q : ℤ × ℤ) : ℤ × ℤ := (a + q.1 * M, b + q.2 * N)

/-- The scaling `(u,v) ↦ (uM, vN)` of the acting `ℤ²`, i.e. `x ↦ x^M`,
`y ↦ y^N`. -/
def scaleIdx (M N : ℤ) (q : ℤ × ℤ) : ℤ × ℤ := (q.1 * M, q.2 * N)

theorem scaleIdx_zero (M N : ℤ) : scaleIdx M N 0 = 0 := by
  show ((0 : ℤ) * M, (0 : ℤ) * N) = (0 : ℤ × ℤ)
  simp

theorem scaleIdx_add (M N : ℤ) (s t : ℤ × ℤ) :
    scaleIdx M N (s + t) = scaleIdx M N s + scaleIdx M N t := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only [scaleIdx, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem scaleIdx_injective {M N : ℤ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Function.Injective (scaleIdx M N) := by
  intro s t hst
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only [scaleIdx, Prod.mk.injEq] at hst
  have h1 : s1 = t1 := mul_right_cancel₀ hM hst.1
  have h2 : s2 = t2 := mul_right_cancel₀ hN hst.2
  rw [h1, h2]

/-- The index scaling intertwines translation by `h` with translation by the
scaled `h`.  This is the compatibility that makes `emb` a homomorphism. -/
theorem embIdx_shiftIdx (a b M N : ℤ) (h q : ℤ × ℤ) :
    embIdx a b M N (shiftIdx h q)
      = shiftIdx (scaleIdx M N h) (embIdx a b M N q) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨q1, q2⟩ := q
  simp only [embIdx, scaleIdx, shiftIdx, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> ring

theorem embIdx_leftInv {a b M N : ℤ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Function.LeftInverse
      (fun q : ℤ × ℤ => ((q.1 - a) / M, (q.2 - b) / N))
      (embIdx a b M N) := by
  intro q
  obtain ⟨q1, q2⟩ := q
  have e1 : a + q1 * M - a = q1 * M := by ring
  have e2 : b + q2 * N - b = q2 * N := by ring
  show ((a + q1 * M - a) / M, (b + q2 * N - b) / N) = (q1, q2)
  rw [e1, e2, Int.mul_ediv_cancel _ hM, Int.mul_ediv_cancel _ hN]

/-- The scaling `x ↦ x^M`, `y ↦ y^N` of the acting `ℤ²`. -/
def scaleHom (M N : ℤ) : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ) where
  toFun q := Multiplicative.ofAdd (scaleIdx M N (Multiplicative.toAdd q))
  map_one' := by
    show Multiplicative.ofAdd (scaleIdx M N (0 : ℤ × ℤ)) = 1
    rw [scaleIdx_zero, ofAdd_zero]
  map_mul' := fun q r => by
    show Multiplicative.ofAdd
        (scaleIdx M N (Multiplicative.toAdd q + Multiplicative.toAdd r))
      = Multiplicative.ofAdd (scaleIdx M N (Multiplicative.toAdd q)) *
        Multiplicative.ofAdd (scaleIdx M N (Multiplicative.toAdd r))
    rw [scaleIdx_add, ofAdd_add]

@[simp] theorem scaleHom_ofAdd (M N : ℤ) (h : ℤ × ℤ) :
    scaleHom M N (Multiplicative.ofAdd h)
      = Multiplicative.ofAdd (scaleIdx M N h) := rfl

theorem scaleHom_injective {M N : ℤ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Function.Injective (scaleHom M N) := by
  intro q r hqr
  have h1 : scaleIdx M N (Multiplicative.toAdd q)
      = scaleIdx M N (Multiplicative.toAdd r) :=
    congrArg (fun m : Multiplicative (ℤ × ℤ) => Multiplicative.toAdd m) hqr
  exact Multiplicative.toAdd.injective (scaleIdx_injective hM hN h1)

/-- The compatibility condition `SemidirectProduct.map` asks for: relabelling
the basis by `embIdx` intertwines translation by `h` with translation by the
scaled `h`. -/
theorem emb_compat (a b M N : ℤ) (q : Multiplicative (ℤ × ℤ)) :
    (indexMap (embIdx a b M N)).comp (shiftHom q).toMonoidHom
      = (shiftHom (scaleHom M N q)).toMonoidHom.comp
          (indexMap (embIdx a b M N)) := by
  refine MonoidHom.ext fun w => ?_
  show indexMap (embIdx a b M N)
      (indexMap (shiftIdx (Multiplicative.toAdd q)) w)
    = indexMap (shiftIdx (scaleIdx M N (Multiplicative.toAdd q)))
        (indexMap (embIdx a b M N) w)
  exact indexMap_comp_congr
    (fun p => embIdx_shiftIdx a b M N (Multiplicative.toAdd q) p) w

/-- **Simpson's canonical isomorphism `G ≅ G_{ab}^{MN}`**, realised as an
injective endomorphism of the base group sending `t ↦ t(a,b)`, `x ↦ x^M`,
`y ↦ y^N`. -/
def emb (a b M N : ℤ) : BaseGroup →* BaseGroup :=
  SemidirectProduct.map (indexMap (embIdx a b M N)) (scaleHom M N)
    (emb_compat a b M N)

@[simp] theorem emb_left (a b M N : ℤ) (z : BaseGroup) :
    (emb a b M N z).left = indexMap (embIdx a b M N) z.left := rfl

@[simp] theorem emb_right (a b M N : ℤ) (z : BaseGroup) :
    (emb a b M N z).right = scaleHom M N z.right := rfl

theorem emb_inl (a b M N : ℤ) (w : FreeGroup (ℤ × ℤ)) :
    emb a b M N (SemidirectProduct.inl w)
      = SemidirectProduct.inl (indexMap (embIdx a b M N) w) := by
  refine SemidirectProduct.ext rfl ?_
  show scaleHom M N (1 : Multiplicative (ℤ × ℤ)) = 1
  exact map_one _

/-- The canonical embedding sends `t` to `t(a,b)`. -/
theorem emb_tGen (a b M N : ℤ) : emb a b M N tGen = tw (a, b) := by
  have h1 : emb a b M N tGen
      = SemidirectProduct.inl
          (indexMap (embIdx a b M N) (FreeGroup.of ((0 : ℤ), (0 : ℤ)))) :=
    emb_inl a b M N (FreeGroup.of ((0 : ℤ), (0 : ℤ)))
  rw [h1, indexMap_of]
  show SemidirectProduct.inl (FreeGroup.of (a + (0 : ℤ) * M, b + (0 : ℤ) * N))
    = SemidirectProduct.inl (FreeGroup.of (a, b))
  rw [zero_mul, zero_mul, add_zero, add_zero]

/-- The canonical embedding sends `x^u y^v` to `x^{uM} y^{vN}`. -/
theorem emb_sh (a b M N : ℤ) (h : ℤ × ℤ) :
    emb a b M N (sh h) = sh (scaleIdx M N h) := by
  refine SemidirectProduct.ext ?_ rfl
  show indexMap (embIdx a b M N) (1 : FreeGroup (ℤ × ℤ)) = 1
  exact map_one _

theorem emb_injective {a b M N : ℤ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Function.Injective (emb a b M N) := by
  intro z w hzw
  refine SemidirectProduct.ext ?_ ?_
  · have hl : indexMap (embIdx a b M N) z.left
        = indexMap (embIdx a b M N) w.left :=
      congrArg SemidirectProduct.left hzw
    exact indexMap_injective (embIdx_leftInv hM hN) hl
  · have hr : scaleHom M N z.right = scaleHom M N w.right :=
      congrArg SemidirectProduct.right hzw
    exact scaleHom_injective hM hN hr

/-! ## `G_{ab}^{MN}`, the residue classes, and Lemma 5 -/

/-- **Simpson's `G_{ab}^{MN}`**, the subgroup generated by `t(a,b)`, `x^M` and
`y^N`, presented here as the range of the canonical embedding.  That the two
descriptions agree is item **S2b** of the roadmap; the inclusion of the three
generators is `emb_tGen` and `emb_sh`. -/
def Gsub (a b M N : ℤ) : Subgroup BaseGroup := (emb a b M N).range

theorem tw_mem_Gsub (a b M N : ℤ) : tw (a, b) ∈ Gsub a b M N :=
  ⟨tGen, emb_tGen a b M N⟩

theorem sh_scale_mem_Gsub (a b M N : ℤ) (h : ℤ × ℤ) :
    sh (scaleIdx M N h) ∈ Gsub a b M N :=
  ⟨sh h, emb_sh a b M N h⟩

/-- **Simpson's three generators `t(a,b)`, `x^M`, `y^N` of `G_{ab}^{MN}` lie in
`Gsub`.**  This is the checkable half of the identification of `Gsub` with
Simpson's `⟨t(a,b), x^M, y^N⟩`; the reverse inclusion is item **S2b** of the
roadmap. -/
theorem closure_le_Gsub (a b M N : ℤ) :
    Subgroup.closure {tw (a, b), sh (M, 0), sh (0, N)} ≤ Gsub a b M N := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · exact tw_mem_Gsub a b M N
  · have h1 : scaleIdx M N (1, 0) = (M, 0) := by
      show ((1 : ℤ) * M, (0 : ℤ) * N) = (M, 0)
      rw [one_mul, zero_mul]
    have h2 := sh_scale_mem_Gsub a b M N (1, 0)
    rwa [h1] at h2
  · have h1 : scaleIdx M N (0, 1) = (0, N) := by
      show ((0 : ℤ) * M, (1 : ℤ) * N) = (0, N)
      rw [zero_mul, one_mul]
    have h2 := sh_scale_mem_Gsub a b M N (0, 1)
    rwa [h1] at h2

/-! ### S2b: the two descriptions of `G_{ab}^{MN}` agree

`Gsub` is defined as the range of the canonical embedding, but Simpson defines
`G_{ab}^{MN}` as the subgroup generated by `t(a,b)`, `x^M` and `y^N`.  One
inclusion is `closure_le_Gsub`; this is the other, and with it the two
definitions are interchangeable.

The route is the one the roadmap describes: the range is the image of `⊤`, the
whole base group is generated by `t`, `x`, `y`, and `Subgroup.map_closure` turns
the image of that generating set into the three elements above.  The step worth
isolating is `sh_zpow`, which is where the `ℤ`-action on `ℤ × ℤ` is used. -/

/-- Powers of a translation are translations. -/
theorem sh_zpow (h : ℤ × ℤ) (n : ℤ) : sh h ^ n = sh (n • h) := by
  simp only [sh, ofAdd_zsmul, map_zpow]

theorem sh_x_zpow (n : ℤ) : xGen ^ n = sh (n, 0) := by
  rw [xGen, sh_zpow]
  congr 1
  simp

theorem sh_y_zpow (n : ℤ) : yGen ^ n = sh (0, n) := by
  rw [yGen, sh_zpow]
  congr 1
  simp

/-- Every translation is a word in `x` and `y`. -/
theorem sh_mem_closure (h : ℤ × ℤ) :
    sh h ∈ Subgroup.closure ({tGen, xGen, yGen} : Set BaseGroup) := by
  have hsplit : sh h = xGen ^ h.1 * yGen ^ h.2 := by
    rw [sh_x_zpow, sh_y_zpow, sh_mul_sh]
    congr 1
    simp
  rw [hsplit]
  exact mul_mem (zpow_mem (Subgroup.subset_closure (by simp)) _)
    (zpow_mem (Subgroup.subset_closure (by simp)) _)

/-- Every free basis element is a conjugate of `t`, by `sh_conj_tw`. -/
theorem tw_mem_closure (p : ℤ × ℤ) :
    tw p ∈ Subgroup.closure ({tGen, xGen, yGen} : Set BaseGroup) := by
  have hc := sh_conj_tw (-p) ((0 : ℤ), (0 : ℤ))
  have hp : ((0 : ℤ), (0 : ℤ)) - (-p) = p := by simp
  have htg : tw ((0 : ℤ), (0 : ℤ)) = tGen := rfl
  rw [hp, htg] at hc
  rw [← hc]
  exact mul_mem (mul_mem (sh_mem_closure _) (Subgroup.subset_closure (by simp)))
    (inv_mem (sh_mem_closure _))

theorem inl_mem_closure (w : FreeGroup (ℤ × ℤ)) :
    (SemidirectProduct.inl w : BaseGroup) ∈
      Subgroup.closure ({tGen, xGen, yGen} : Set BaseGroup) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · rw [map_one]; exact one_mem _
  · intro p; exact tw_mem_closure p
  · intro p ih; rw [map_inv]; exact inv_mem ih
  · intro u v ihu ihv; rw [map_mul]; exact mul_mem ihu ihv

/-- **The base group is generated by `t`, `x` and `y`.** -/
theorem top_eq_closure_gens :
    (⊤ : Subgroup BaseGroup) = Subgroup.closure {tGen, xGen, yGen} := by
  refine le_antisymm (fun g _ => ?_) le_top
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  refine mul_mem (inl_mem_closure _) ?_
  have : (SemidirectProduct.inr g.right : BaseGroup)
      = sh (Multiplicative.toAdd g.right) := rfl
  rw [this]
  exact sh_mem_closure _

theorem emb_xGen (a b M N : ℤ) : emb a b M N xGen = sh (M, 0) := by
  rw [xGen, emb_sh]
  congr 1
  show ((1 : ℤ) * M, (0 : ℤ) * N) = (M, 0)
  rw [one_mul, zero_mul]

theorem emb_yGen (a b M N : ℤ) : emb a b M N yGen = sh (0, N) := by
  rw [yGen, emb_sh]
  congr 1
  show ((0 : ℤ) * M, (1 : ℤ) * N) = (0, N)
  rw [zero_mul, one_mul]

/-- **S2b.**  The range of the canonical embedding is exactly Simpson's
`G_{ab}^{MN} = ⟨t(a,b), x^M, y^N⟩`, so the two descriptions may be used
interchangeably. -/
theorem Gsub_eq_closure (a b M N : ℤ) :
    Gsub a b M N = Subgroup.closure {tw (a, b), sh (M, 0), sh (0, N)} := by
  refine le_antisymm ?_ (closure_le_Gsub a b M N)
  rw [Gsub, MonoidHom.range_eq_map, top_eq_closure_gens,
    Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  refine Subgroup.mem_comap.mpr ?_
  rcases hg with rfl | rfl | rfl
  · rw [emb_tGen]; exact Subgroup.subset_closure (by simp)
  · rw [emb_xGen]; exact Subgroup.subset_closure (by simp)
  · rw [emb_yGen]; exact Subgroup.subset_closure (by simp)

/-- **Simpson's index set for `T_{ab}^{MN}`**: the pairs congruent to `(a,b)`
modulo `(M,N)`. -/
def residue (a b M N : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ u v : ℤ, p = (a + u * M, b + v * N)}

theorem range_embIdx (a b M N : ℤ) :
    Set.range (embIdx a b M N) = residue a b M N := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨(u, v), rfl⟩

theorem range_indexMap_embIdx (a b M N : ℤ) :
    (indexMap (embIdx a b M N)).range = basisSubgroup (residue a b M N) := by
  rw [range_indexMap, range_embIdx]

/-- **Simpson, Lemma 5.**  `T_{ab}^{MN} = T ∩ G_{ab}^{MN}`.

Simpson's proof is: `⊆` because `t(uM+a, vN+b) = x^{-uM} y^{-vN} t(a,b) x^{uM}
y^{vN}`, and `⊇` because every element of `G_{ab}^{MN}` is `g x^{uM} y^{vN}`
with `g ∈ T_{ab}^{MN}`, and lying in `T` forces `u = v = 0`.  In the split-
extension model that argument is exactly the computation below: the `ℤ²`
component of an element of `G_{ab}^{MN}` is a scaled one, membership in `T`
kills it, and the scaling is injective, so the element comes from the free part
alone --- whose image is `basisSubgroup` of the range of the index scaling,
i.e. of the residue class.

No hypothesis on `M` and `N` is needed: the argument never inverts the scaling,
it only observes that an element of `G_{ab}^{MN}` whose `ℤ²` component is
trivial is the image of a purely free element. -/
theorem Tsub_inf_Gsub (a b M N : ℤ) :
    Tsub ⊓ Gsub a b M N = twSub (residue a b M N) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hT, hG⟩ := hg
    obtain ⟨z, rfl⟩ := hG
    have hr : (emb a b M N z).right = 1 := mem_Tsub_iff.1 hT
    have hmem : indexMap (embIdx a b M N) z.left
        ∈ basisSubgroup (residue a b M N) := by
      rw [← range_indexMap_embIdx]
      exact ⟨z.left, rfl⟩
    refine Subgroup.mem_map.2 ⟨indexMap (embIdx a b M N) z.left, hmem, ?_⟩
    exact SemidirectProduct.ext rfl hr.symm
  · refine le_inf (twSub_le_Tsub _) ?_
    intro g hg
    rw [twSub, Subgroup.mem_map] at hg
    obtain ⟨w, hw, rfl⟩ := hg
    rw [← range_indexMap_embIdx] at hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨SemidirectProduct.inl v, emb_inl a b M N v⟩

/-! ## S5b: transporting the base-group computations along `emb`

`BooneGroupMachineIndex` computes `T ⊓ G_{ab}^{MN}` and `T_M ⊓ G_{ab}^{MN}` and
exhibits the source and target sides of a quadruple as the two images of one
parameter set.  To feed that into S4 one needs to know that `emb` carries `twSub`
to `twSub` of the image, which is `map_basisSubgroup` transported along
`emb_inl`. -/

theorem twSub_map_emb (a b M N : ℤ) (S : Set (ℤ × ℤ)) :
    (twSub S).map (emb a b M N) = twSub (embIdx a b M N '' S) := by
  rw [twSub, twSub, ← map_basisSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext (emb_inl a b M N)

/-- `T_S` is generated by the basis elements it names. -/
theorem twSub_eq_closure (S : Set (ℤ × ℤ)) :
    twSub S = Subgroup.closure (tw '' S) := by
  rw [twSub, basisSubgroup, MonoidHom.map_closure, Set.image_image]
  rfl

/-- `emb` acts on the basis by `embIdx`. -/
theorem emb_tw (a b M N : ℤ) (p : ℤ × ℤ) :
    emb a b M N (tw p) = tw (embIdx a b M N p) := by
  rw [tw, emb_inl, indexMap_of]
  rfl

theorem emb_mem_twSub_iff {a b M N : ℤ} (hM : M ≠ 0) (hN : N ≠ 0)
    (S : Set (ℤ × ℤ)) (g : BaseGroup) :
    emb a b M N g ∈ twSub (embIdx a b M N '' S) ↔ g ∈ twSub S := by
  rw [← twSub_map_emb, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rwa [emb_injective hM hN hxg] at hx
  · intro hg
    exact ⟨g, hg, rfl⟩

end Base
end BooneGroup
end GroupApproximation
