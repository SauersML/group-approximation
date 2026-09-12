import GroupApproximation.CharClass.SliceGenOfLines
import GroupApproximation.CharClass.ChernEulerIsoOf
import GroupApproximation.CharClass.ChernClassesEvenOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The roots of `V` over a field `K`, at sphere rank `n`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm; the coefficient-generic form of
`SliceRoots`, `SliceRootsBlock`, `SliceTrivialEuler` and `SliceVGenerator`.

The root of a line `L` over `K` is its Euler class at `tautEulerOfK`'s index,
`eulerOfBundleOf K hgen (pushforward (tautEmbOf ι) _ L) _`, for a chosen class
`hgen ∈ H²(ℂP^{1 + card ι}; K)`; this is `lineEulerOfK K hgen L _` by definition, spelled out here
so that this file does not wait for the module naming it.

* **The constant lines have root zero.**  Their classifying map is constant, so it factors through
  a point, which has no `H²`.
* **The line of block `(j, i)` has as root the class of the tautological line of `ℂP^{dd j}`,
  pulled back along the projection to that factor.**  The block line is that line pushed into the
  block (`Gen.vLineYBundle_inr_eq`); over `K` the Euler class does not depend on the injection
  (`CPn.eulerOfBundle_pushforward_congrOf`), and it is natural (`eulerOfBundle_comapOf`).

So every block over the factor `j` gives the same root, `sliceGenOf K n hgen j`, which is what the
slice polynomial sees with multiplicity `dd j`.  No generator is canonical over `K`, and none is
needed: the value holds for every `hgen`.

## Main declarations

* `Gen.eulerOfBundleOf_congr`, `Gen.eulerOfBundleOf_pushforward_eq_zero_of_const`.
* `Gen.vRootOf`, `Gen.vRootOf_inl`, `Gen.vRootOf_inr` — the roots.
* `Gen.sliceGenOf`, `Gen.evenTautOf_vRootOf_inr` — **the generator of the `j`-th factor.**
* `Gen.vRootFlatOf`, `Gen.vRootFlatOf_equiv` — the roots over a flat range.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.CPn

set_option linter.unusedSectionVars false

namespace Gen

section Generic

variable (K : Type) [Field K] {X : Type} [TopologicalSpace X]

/-- Equal bundles have equal Euler classes over `K`; the trace proofs are irrelevant. -/
theorem eulerOfBundleOf_congr {d : ℕ} (hgen : Hmod K (CPtop d) 2) {p q : Bundle X (Fin (d + 1))}
    (h : p = q) (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1) :
    eulerOfBundleOf K hgen p hp = eulerOfBundleOf K hgen q hq := by
  subst h
  rfl

/-- **A constant line has vanishing Euler class over `K`**, at `tautEulerOfK`'s index.  Its
classifying map is constant, so it factors through a point. -/
theorem eulerOfBundleOf_pushforward_eq_zero_of_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (x₀ : X) (L : Bundle X ι)
    (hL : ∀ x, (L x).trace = 1) (hconst : ∀ x y : X, L x = L y) :
    eulerOfBundleOf K hgen (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) L)
      (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) L hL) = 0 := by
  classical
  set P := pushforward (tautEmbOf ι) (tautEmbOf_injective ι) L with hPdef
  set hPtr := trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) L hL with hPtrdef
  have hPconst : ∀ x : X, P x = P x₀ := by
    intro x
    show coordIncl (tautEmbOf ι) * L x * (coordIncl (tautEmbOf ι))ᴴ
      = coordIncl (tautEmbOf ι) * L x₀ * (coordIncl (tautEmbOf ι))ᴴ
    rw [hconst x x₀]
  refine eulerOfBundle_eq_zero_of_factorsOf K hgen P hPtr
    (TopCat.ofHom ⟨fun _ => (), continuous_const⟩)
    (TopCat.ofHom ⟨fun _ => classifyOne P hPtr x₀, continuous_const⟩) ?_
    (fun a => cohomology_eq_zero_of_contractibleOf K Unit 2 (by omega) a)
  exact TopCat.hom_ext (ContinuousMap.ext fun x => Subtype.ext (hPconst x))

end Generic

variable (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **The roots of `V` over `K`**: the Euler class of each line at `tautEulerOfK`'s index.  This is
`lineEulerOfK K hgen (vLineYBundle n b) _` by definition. -/
def vRootOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (b : Fin (n + 1) ⊕ HBlk dd) :
    Hmod K (TopCat.of (baseY dd)) 2 :=
  eulerOfBundleOf K hgen
    (pushforward (tautEmbOf (VIdx n dd)) (tautEmbOf_injective (VIdx n dd)) (vLineYBundle n b))
    (trace_pushforward_one (tautEmbOf (VIdx n dd)) (tautEmbOf_injective (VIdx n dd))
      (vLineYBundle n b) (trace_vLineYBundle n b))

/-- **The constant lines have root zero.** -/
theorem vRootOf_inl (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (i : Fin (n + 1)) :
    vRootOf K n hgen (Sum.inl i : Fin (n + 1) ⊕ HBlk dd) = 0 :=
  eulerOfBundleOf_pushforward_eq_zero_of_const K hgen (baseYPoint dd)
    (vLineYBundle n (Sum.inl i)) (trace_vLineYBundle n (Sum.inl i)) (fun _ _ => rfl)

/-- **The root of a block line** is the class of the tautological line of its factor, pushed into
the block, pulled back along the projection to the factor. -/
theorem vRootOf_inr (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (β : HBlk dd) :
    vRootOf K n hgen (Sum.inr β)
      = pull (cmap (evalFactor dd β.1)) 2
          (eulerOfBundleOf K hgen
            (pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n β)
              ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β)) (cpTaut (dd β.1)))
            (trace_pushforward_one _
              ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β))
              (cpTaut (dd β.1)) (trace_cpTaut (dd β.1)))) := by
  have hN : 1 ≤ 1 + tautCardOf (VIdx n dd) := by omega
  have h1 : vRootOf K n hgen (Sum.inr β)
      = eulerOfBundleOf K hgen
          (pushforward (tautEmbOf (VIdx n dd)) (tautEmbOf_injective (VIdx n dd))
            (pushforward (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)))
          (trace_pushforward_one _ _ _
            (trace_pushforward_one (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)
              (trace_cpTautY dd β.1))) :=
    eulerOfBundleOf_congr K hgen
      (congrArg (pushforward (tautEmbOf (VIdx n dd)) (tautEmbOf_injective (VIdx n dd)))
        (vLineYBundle_inr_eq n β)) _ _
  have h2 : eulerOfBundleOf K hgen
          (pushforward (tautEmbOf (VIdx n dd)) (tautEmbOf_injective (VIdx n dd))
            (pushforward (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)))
          (trace_pushforward_one _ _ _
            (trace_pushforward_one (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)
              (trace_cpTautY dd β.1)))
      = eulerOfBundleOf K hgen
          (pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n β)
            ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β)) (cpTautY dd β.1))
          (trace_pushforward_one _ _ (cpTautY dd β.1) (trace_cpTautY dd β.1)) :=
    eulerOfBundle_pushforward_congrOf K hN hgen _ _ _ _ _ _
      (pushforwardIso (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)).symm
  have h3 : pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n β)
        ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β)) (cpTautY dd β.1)
      = comap (evalFactor dd β.1)
          (pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n β)
            ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β))
            (cpTaut (dd β.1))) :=
    Bundle.ext fun _ => rfl
  have h4 := eulerOfBundle_comapOf K hgen
    (pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n β)
      ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β)) (cpTaut (dd β.1)))
    (trace_pushforward_one _ ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β))
      (cpTaut (dd β.1)) (trace_cpTaut (dd β.1)))
    (evalFactor dd β.1)
  exact h1.trans (h2.trans ((eulerOfBundleOf_congr K hgen h3 _ _).trans h4))

/-- The injection of the block `β` into `tautEulerOfK`'s index. -/
def blockTautEmb (β : HBlk dd) : Fin (dd β.1 + 1) → Fin (1 + tautCardOf (VIdx n dd) + 1) :=
  tautEmbOf (VIdx n dd) ∘ blockEmb n β

theorem blockTautEmb_injective (β : HBlk dd) : Function.Injective (blockTautEmb n β) :=
  (tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n β)

/-- The class of the tautological line of the factor of `β`, pushed into the block `β` at
`tautEulerOfK`'s index, pulled back along the projection to the factor. -/
def blockClassOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (β : HBlk dd) :
    Hmod K (TopCat.of (baseY dd)) 2 :=
  pull (cmap (evalFactor dd β.1)) 2
    (eulerOfBundleOf K hgen
      (pushforward (blockTautEmb n β) (blockTautEmb_injective n β) (cpTaut (dd β.1)))
      (trace_pushforward_one (blockTautEmb n β) (blockTautEmb_injective n β) (cpTaut (dd β.1))
        (trace_cpTaut (dd β.1))))

/-- The root of a block line is its block class. -/
theorem vRootOf_inr_eq_blockClassOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2)
    (β : HBlk dd) : vRootOf K n hgen (Sum.inr β) = blockClassOf K n hgen β :=
  vRootOf_inr K n hgen β

/-- **Over `K` the block class does not see which block over the factor it is taken in.** -/
theorem blockClassOf_congr (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (j : Fin ℓ)
    (i i' : Fin (dd j)) :
    blockClassOf K n hgen (⟨j, i⟩ : HBlk dd) = blockClassOf K n hgen (⟨j, i'⟩ : HBlk dd) :=
  congrArg (pull (cmap (evalFactor dd j)) 2)
    (eulerOfBundle_pushforward_congrOf K (show 1 ≤ 1 + tautCardOf (VIdx n dd) by omega) hgen
      (cpTaut (dd j)) (cpTaut (dd j))
      (blockTautEmb_injective n (⟨j, i⟩ : HBlk dd)) (blockTautEmb_injective n (⟨j, i'⟩ : HBlk dd))
      (trace_pushforward_one (blockTautEmb n (⟨j, i⟩ : HBlk dd))
        (blockTautEmb_injective n (⟨j, i⟩ : HBlk dd)) (cpTaut (dd j)) (trace_cpTaut (dd j)))
      (trace_pushforward_one (blockTautEmb n (⟨j, i'⟩ : HBlk dd))
        (blockTautEmb_injective n (⟨j, i'⟩ : HBlk dd)) (cpTaut (dd j)) (trace_cpTaut (dd j)))
      (BundleIso.refl _))

/-- **The generator of the `j`-th projective factor over `K`**: the Euler class of the tautological
line of `ℂP^{dd j}`, pushed into the first block over `j`, pulled back to the base.  Zero when
`dd j = 0`: there is no block over `j`, and the slice polynomial reads `gen j` only through the
power `dd j`. -/
def sliceGenOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (j : Fin ℓ) :
    Gen.evenPart K (TopCat.of (baseY dd)) :=
  if h : 0 < dd j then evenTautOf K (blockClassOf K n hgen (⟨j, ⟨0, h⟩⟩ : HBlk dd)) else 0

/-- **Every block line over the factor `j` has root `sliceGenOf K n hgen j`**: the Euler class over
`K` does not see which block the line is pushed into. -/
theorem evenTautOf_vRootOf_inr (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2)
    (β : HBlk dd) :
    evenTautOf K (vRootOf K n hgen (Sum.inr β)) = sliceGenOf K n hgen β.1 := by
  obtain ⟨j, i⟩ := β
  have hpos : 0 < dd j := Fin.pos i
  show evenTautOf K (vRootOf K n hgen (Sum.inr ⟨j, i⟩)) = sliceGenOf K n hgen j
  rw [sliceGenOf, dif_pos hpos, vRootOf_inr_eq_blockClassOf,
    blockClassOf_congr K n hgen j i ⟨0, hpos⟩]

/-- The roots, indexed by a natural, reading the index modulo the rank.  This is
`lineEulerOfK K hgen (vLineFlatBundle n dd l) _` by definition. -/
def vRootFlatOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (l : ℕ) :
    Hmod K (TopCat.of (baseY dd)) 2 :=
  vRootOf K n hgen ((vIndexEquiv n dd).symm
    ⟨l % KGen.lixRank n dd, Nat.mod_lt _ (kgenLixRank_pos n dd)⟩)

/-- At an index coming from the block type, the flat root is the block's root. -/
theorem vRootFlatOf_equiv (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2)
    (b : Fin (n + 1) ⊕ HBlk dd) :
    vRootFlatOf K n hgen ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ)
      = vRootOf K n hgen b := by
  have hlt : ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) < KGen.lixRank n dd :=
    (vIndexEquiv n dd b).isLt
  have h : (⟨((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) % KGen.lixRank n dd,
      Nat.mod_lt _ (kgenLixRank_pos n dd)⟩ : Fin (KGen.lixRank n dd)) = vIndexEquiv n dd b :=
    Fin.ext (Nat.mod_eq_of_lt hlt)
  rw [vRootFlatOf, h, Equiv.symm_apply_apply]

/-! ## The roots after pushing `V` into a larger index

The mapping torus lives at the doubled index `VIdx n dd ⊕ VIdx n dd`, and its restriction to the
slice is `V` pushed into one block.  The roots of the pushed lines are computed exactly as above,
at the larger index and with the composite injection, so no generator is compared across two
projective spaces of different sizes. -/

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **The roots of `V` pushed along an injection `u`**, over `K`, at the larger index. -/
def vRootPushOf (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (b : Fin (n + 1) ⊕ HBlk dd) :
    Hmod K (TopCat.of (baseY dd)) 2 :=
  eulerOfBundleOf K hgen
    (pushforward (tautEmbOf κ) (tautEmbOf_injective κ) (pushforward u hu (vLineYBundle n b)))
    (trace_pushforward_one (tautEmbOf κ) (tautEmbOf_injective κ) (pushforward u hu (vLineYBundle n b))
      (trace_pushforward_one u hu (vLineYBundle n b) (trace_vLineYBundle n b)))

/-- The pushed constant lines have root zero. -/
theorem vRootPushOf_inl (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (i : Fin (n + 1)) :
    vRootPushOf K n u hu hgen (Sum.inl i : Fin (n + 1) ⊕ HBlk dd) = 0 :=
  eulerOfBundleOf_pushforward_eq_zero_of_const K hgen (baseYPoint dd)
    (pushforward u hu (vLineYBundle n (Sum.inl i)))
    (trace_pushforward_one u hu (vLineYBundle n (Sum.inl i)) (trace_vLineYBundle n (Sum.inl i)))
    (fun _ _ => rfl)

/-- The root of a pushed block line is the class of the tautological line of its factor, pushed
along the composite injection, pulled back along the projection to the factor. -/
theorem vRootPushOf_inr (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (β : HBlk dd) :
    vRootPushOf K n u hu hgen (Sum.inr β)
      = pull (cmap (evalFactor dd β.1)) 2
          (eulerOfBundleOf K hgen
            (pushforward (tautEmbOf κ ∘ u ∘ blockEmb n β)
              ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β))) (cpTaut (dd β.1)))
            (trace_pushforward_one _
              ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β)))
              (cpTaut (dd β.1)) (trace_cpTaut (dd β.1)))) := by
  have hN : 1 ≤ 1 + tautCardOf κ := by omega
  have h1 : vRootPushOf K n u hu hgen (Sum.inr β)
      = eulerOfBundleOf K hgen
          (pushforward (tautEmbOf κ) (tautEmbOf_injective κ)
            (pushforward u hu
              (pushforward (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1))))
          (trace_pushforward_one _ _ _ (trace_pushforward_one u hu _
            (trace_pushforward_one (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)
              (trace_cpTautY dd β.1)))) :=
    eulerOfBundleOf_congr K hgen
      (congrArg (fun F => pushforward (tautEmbOf κ) (tautEmbOf_injective κ) (pushforward u hu F))
        (vLineYBundle_inr_eq n β)) _ _
  have h2 : eulerOfBundleOf K hgen
          (pushforward (tautEmbOf κ) (tautEmbOf_injective κ)
            (pushforward u hu
              (pushforward (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1))))
          (trace_pushforward_one _ _ _ (trace_pushforward_one u hu _
            (trace_pushforward_one (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)
              (trace_cpTautY dd β.1))))
      = eulerOfBundleOf K hgen
          (pushforward (tautEmbOf κ ∘ u ∘ blockEmb n β)
            ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β))) (cpTautY dd β.1))
          (trace_pushforward_one _ _ (cpTautY dd β.1) (trace_cpTautY dd β.1)) :=
    eulerOfBundle_pushforward_congrOf K hN hgen _ _ _ _ _ _
      ((pushforwardIso u hu _).symm.trans
        (pushforwardIso (blockEmb n β) (blockEmb_injective n β) (cpTautY dd β.1)).symm)
  have h3 : pushforward (tautEmbOf κ ∘ u ∘ blockEmb n β)
        ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β))) (cpTautY dd β.1)
      = comap (evalFactor dd β.1)
          (pushforward (tautEmbOf κ ∘ u ∘ blockEmb n β)
            ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β)))
            (cpTaut (dd β.1))) :=
    Bundle.ext fun _ => rfl
  have h4 := eulerOfBundle_comapOf K hgen
    (pushforward (tautEmbOf κ ∘ u ∘ blockEmb n β)
      ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β))) (cpTaut (dd β.1)))
    (trace_pushforward_one _ ((tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β)))
      (cpTaut (dd β.1)) (trace_cpTaut (dd β.1)))
    (evalFactor dd β.1)
  exact h1.trans (h2.trans ((eulerOfBundleOf_congr K hgen h3 _ _).trans h4))

/-- The injection of the block `β`, pushed along `u`, into `tautEulerOfK`'s index. -/
def blockPushEmb (u : VIdx n dd → κ) (β : HBlk dd) : Fin (dd β.1 + 1) → Fin (1 + tautCardOf κ + 1) :=
  tautEmbOf κ ∘ u ∘ blockEmb n β

theorem blockPushEmb_injective (u : VIdx n dd → κ) (hu : Function.Injective u) (β : HBlk dd) :
    Function.Injective (blockPushEmb n u β) :=
  (tautEmbOf_injective κ).comp (hu.comp (blockEmb_injective n β))

/-- The class of the tautological line of the factor of `β`, pushed into the block `β` and along
`u`, pulled back along the projection to the factor. -/
def blockClassPushOf (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (β : HBlk dd) : Hmod K (TopCat.of (baseY dd)) 2 :=
  pull (cmap (evalFactor dd β.1)) 2
    (eulerOfBundleOf K hgen
      (pushforward (blockPushEmb n u β) (blockPushEmb_injective n u hu β) (cpTaut (dd β.1)))
      (trace_pushforward_one (blockPushEmb n u β) (blockPushEmb_injective n u hu β)
        (cpTaut (dd β.1)) (trace_cpTaut (dd β.1))))

/-- The root of a pushed block line is its block class. -/
theorem vRootPushOf_inr_eq_blockClassPushOf (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (β : HBlk dd) :
    vRootPushOf K n u hu hgen (Sum.inr β) = blockClassPushOf K n u hu hgen β :=
  vRootPushOf_inr K n u hu hgen β

/-- Over `K` the pushed block class does not see which block over the factor it is taken in. -/
theorem blockClassPushOf_congr (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (j : Fin ℓ) (i i' : Fin (dd j)) :
    blockClassPushOf K n u hu hgen (⟨j, i⟩ : HBlk dd)
      = blockClassPushOf K n u hu hgen (⟨j, i'⟩ : HBlk dd) :=
  congrArg (pull (cmap (evalFactor dd j)) 2)
    (eulerOfBundle_pushforward_congrOf K (show 1 ≤ 1 + tautCardOf κ by omega) hgen
      (cpTaut (dd j)) (cpTaut (dd j))
      (blockPushEmb_injective n u hu (⟨j, i⟩ : HBlk dd))
      (blockPushEmb_injective n u hu (⟨j, i'⟩ : HBlk dd))
      (trace_pushforward_one (blockPushEmb n u (⟨j, i⟩ : HBlk dd))
        (blockPushEmb_injective n u hu (⟨j, i⟩ : HBlk dd)) (cpTaut (dd j)) (trace_cpTaut (dd j)))
      (trace_pushforward_one (blockPushEmb n u (⟨j, i'⟩ : HBlk dd))
        (blockPushEmb_injective n u hu (⟨j, i'⟩ : HBlk dd)) (cpTaut (dd j)) (trace_cpTaut (dd j)))
      (BundleIso.refl _))

/-- **The generator of the `j`-th factor after pushing along `u`**: the class every pushed block
line over `j` carries.  Zero when `dd j = 0`. -/
def sliceGenPushOf (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (j : Fin ℓ) :
    Gen.evenPart K (TopCat.of (baseY dd)) :=
  if h : 0 < dd j then evenTautOf K (blockClassPushOf K n u hu hgen (⟨j, ⟨0, h⟩⟩ : HBlk dd))
  else 0

/-- Every pushed block line over the factor `j` has root `sliceGenPushOf K n u hu hgen j`. -/
theorem evenTautOf_vRootPushOf_inr (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (β : HBlk dd) :
    evenTautOf K (vRootPushOf K n u hu hgen (Sum.inr β)) = sliceGenPushOf K n u hu hgen β.1 := by
  obtain ⟨j, i⟩ := β
  have hpos : 0 < dd j := Fin.pos i
  show evenTautOf K (vRootPushOf K n u hu hgen (Sum.inr ⟨j, i⟩)) = sliceGenPushOf K n u hu hgen j
  rw [sliceGenPushOf, dif_pos hpos, vRootPushOf_inr_eq_blockClassPushOf,
    blockClassPushOf_congr K n u hu hgen j i ⟨0, hpos⟩]

/-- The pushed roots, indexed by a natural, reading the index modulo the rank.  This is
`lineEulerOfK K hgen (pushforward u hu (vLineFlatBundle n dd l)) _` by definition. -/
def vRootFlatPushOf (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (l : ℕ) : Hmod K (TopCat.of (baseY dd)) 2 :=
  vRootPushOf K n u hu hgen ((vIndexEquiv n dd).symm
    ⟨l % KGen.lixRank n dd, Nat.mod_lt _ (kgenLixRank_pos n dd)⟩)

theorem vRootFlatPushOf_equiv (u : VIdx n dd → κ) (hu : Function.Injective u)
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (b : Fin (n + 1) ⊕ HBlk dd) :
    vRootFlatPushOf K n u hu hgen ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ)
      = vRootPushOf K n u hu hgen b := by
  have hlt : ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) < KGen.lixRank n dd :=
    (vIndexEquiv n dd b).isLt
  have h : (⟨((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) % KGen.lixRank n dd,
      Nat.mod_lt _ (kgenLixRank_pos n dd)⟩ : Fin (KGen.lixRank n dd)) = vIndexEquiv n dd b :=
    Fin.ext (Nat.mod_eq_of_lt hlt)
  rw [vRootFlatPushOf, h, Equiv.symm_apply_apply]

end Gen

#audit_axioms Gen.vRootOf_inl
#audit_axioms Gen.vRootOf_inr
#audit_axioms Gen.evenTautOf_vRootOf_inr

end GroupApproximation.CharClass
