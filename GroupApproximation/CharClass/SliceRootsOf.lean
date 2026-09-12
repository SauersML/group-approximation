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

/-- **The generator of the `j`-th projective factor over `K`**: the Euler class of the tautological
line of `ℂP^{dd j}`, pushed into the first block over `j`, pulled back to the base.  Zero when
`dd j = 0`: there is no block over `j`, and the slice polynomial reads `gen j` only through the
power `dd j`. -/
def sliceGenOf (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2) (j : Fin ℓ) :
    Gen.evenPart K (TopCat.of (baseY dd)) :=
  if h : 0 < dd j then
    evenTautOf K (pull (cmap (evalFactor dd j)) 2
      (eulerOfBundleOf K hgen
        (pushforward (tautEmbOf (VIdx n dd) ∘ blockEmb n (⟨j, ⟨0, h⟩⟩ : HBlk dd))
          ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n _)) (cpTaut (dd j)))
        (trace_pushforward_one _
          ((tautEmbOf_injective (VIdx n dd)).comp (blockEmb_injective n _))
          (cpTaut (dd j)) (trace_cpTaut (dd j)))))
  else 0

/-- **Every block line over the factor `j` has root `sliceGenOf K n hgen j`**: the Euler class over
`K` does not see which block the line is pushed into. -/
theorem evenTautOf_vRootOf_inr (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd))) 2)
    (β : HBlk dd) :
    evenTautOf K (vRootOf K n hgen (Sum.inr β)) = sliceGenOf K n hgen β.1 := by
  have hpos : 0 < dd β.1 := Fin.pos β.2
  rw [sliceGenOf, dif_pos hpos, vRootOf_inr]
  exact congrArg (fun c => evenTautOf K (pull (cmap (evalFactor dd β.1)) 2 c))
    (eulerOfBundle_pushforward_congrOf K (by omega) hgen (cpTaut (dd β.1)) (cpTaut (dd β.1))
      _ _ _ _ (BundleIso.refl _))

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

end Gen

#audit_axioms Gen.vRootOf_inl
#audit_axioms Gen.vRootOf_inr
#audit_axioms Gen.evenTautOf_vRootOf_inr

end GroupApproximation.CharClass
