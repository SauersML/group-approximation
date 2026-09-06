import GroupApproximation.CharClass.CartanMidFourSlots
import GroupApproximation.CharClass.CartanComposeA

/-!
# The middle-four interchange is natural

`cc-steenrod`'s second composite needs its naturality, and the interchange sits
in the middle of it, so the interchange has to commute with pushing forward along
a map of spaces.  It does, and for a reason with no arithmetic in it: pushing a
simplex forward does not change its degree, so the regrouping and the pushforward
touch disjoint parts of the index and commute on the nose.

That is why this lemma is short while the chain-map property is not.  The
differential moves a degree and forces the two sides to spell it differently; the
pushforward moves nothing.

## Main results

* `pairPush`, `fourPush` — pushing a pair and a fourfold index forward.
* `midIdx_fourPush` — **the index-level naturality**, which is `rfl`.
* `midSwap_pairHom` — the naturality on chains, in the shape `cc-steenrod`
  consumes.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-! ## 1. Pushing indices forward -/

/-- Push both simplices of a pair index forward; the two degrees do not move. -/
def pairPush {k : ℕ} (u : TensorIdx (singFreeCx X) (singFreeCx X) k) :
    TensorIdx (singFreeCx Y) (singFreeCx Y) k :=
  ⟨u.1, (pushSimplex f u.1.val.1 u.2.1, pushSimplex f u.1.val.2 u.2.2)⟩

/-- Push all four simplices of a fourfold index forward. -/
def fourPush {k : ℕ} (W : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    TensorIdx (pairFreeCx Y) (pairFreeCx Y) k :=
  ⟨W.1, (pairPush f W.2.1, pairPush f W.2.2)⟩

/-- **The index-level naturality.**  Regrouping and pushing forward commute on
the nose, because the pushforward does not move a degree. -/
theorem midIdx_fourPush {k : ℕ} (W : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    midIdx (singFreeCx Y) (singFreeCx Y) (singFreeCx Y) (singFreeCx Y) (fourPush f W)
      = fourPush f
          (midIdx (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) W) := rfl

/-! ## 2. The pushforward on a basis element -/

theorem singHom_single (a : ℕ) (x : (singFreeCx X).ι a) :
    (singHom f).f a (Finsupp.single x (1 : ZMod 2))
      = Finsupp.single (pushSimplex f a x) 1 := Finsupp.mapDomain_single

theorem pairHom_single (m : ℕ) (u : TensorIdx (singFreeCx X) (singFreeCx X) m) :
    (pairHom f).f m (Finsupp.single u (1 : ZMod 2))
      = Finsupp.single (pairPush f u) 1 := by
  obtain ⟨pu, x1, x2⟩ := u
  show tenHom (singHom f) (singHom f) m
      (Finsupp.single (⟨pu, (x1, x2)⟩ :
        TensorIdx (singFreeCx X) (singFreeCx X) m) 1) = _
  rw [tenHom_single, one_smul]
  show tenElt (singFreeCx Y) (singFreeCx Y) pu
      ((singHom f).f pu.val.1 (Finsupp.single x1 1))
      ((singHom f).f pu.val.2 (Finsupp.single x2 1)) = _
  rw [singHom_single, singHom_single, tenElt_single_single]
  rfl

theorem tenHomGen_pairHom (k : ℕ) (W : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    tenHomGen (pairHom f) (pairHom f) k W = Finsupp.single (fourPush f W) 1 := by
  obtain ⟨p, u, v⟩ := W
  show tenElt (pairFreeCx Y) (pairFreeCx Y) p
      ((pairHom f).f p.val.1 (Finsupp.single u 1))
      ((pairHom f).f p.val.2 (Finsupp.single v 1)) = _
  rw [pairHom_single, pairHom_single, tenElt_single_single]
  rfl

/-! ## 3. Naturality on chains -/

/-- **The interchange is natural.**  This is the shape `cc-steenrod`'s second
composite consumes: all four factors are the singular complex, so the source and
target of the interchange are the same type. -/
theorem midSwap_pairHom (k : ℕ)
    (z : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    tenHom (pairHom f) (pairHom f) k
        (midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k z)
      = midSwap (singFreeCx Y) (singFreeCx Y) (singFreeCx Y) (singFreeCx Y) k
          (tenHom (pairHom f) (pairHom f) k z) := by
  induction z using Finsupp.induction_linear with
  | zero => rfl
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single W c =>
      rw [midSwap_single, tenHom_single, tenHom_single, map_smul,
        tenHomGen_pairHom, tenHomGen_pairHom, midSwap_single, midIdx_fourPush]

end

end GroupApproximation.CharClass
