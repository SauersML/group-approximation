import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseSector
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchIsolated
import GroupApproximation.Meta.AxiomGuard

/-!
# Crossers of a sector come in pairs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-20.

Write `σ` for the rotation and `α` for the reversal.  Let `c` be the boundary cycle of a set `F`
of faces: `z ∈ c` exactly when `z` lies in `F` and `α z` does not.  Take a sector of the rotation
from `x` to `y`, where `α x` and `y` lie in `F`.  A passage `p → next p` *crosses* the sector when
exactly one of `α p` and `next p` lies strictly inside it.

## Route

* `regionMoveLoose_even_crossers`: the number of crossing passages is even.
  *Proof.*  The number of `p ∈ c` with `α p` inside the sector equals the number of sector darts
  `z` with `α z ∈ c`.  The number of `p ∈ c` with `next p` inside equals the number of sector darts
  in `c`, since `next` permutes `c`.  So, mod 2, the crossers count the sector darts `z` for which
  exactly one of `z` and `α z` lies in `c`.  That happens exactly when `[z ∈ F] ≠ [σ z ∈ F]`,
  because `α z` and `σ z` bound the same face.  Along `σ x, …, σ^(k-1) x` this telescopes to
  `[σ x ∈ F] = [y ∈ F]`, and both are true.
* `regionMoveLoose_false_of_pair`: in a pocket with a closed boundary walk, a turn `d₀` crossed by
  `d ≠ d₀` cannot have every other passage tight.  A tight passage crosses nothing, and `d₀` does
  not cross its own sector.  So `d` would be the only crosser, and `1` is odd.

## Truth check

Proved lemmas.  They use that `σ` and `α` are permutations, `α` is an involution, `σ z` and `α z`
bound the same face, and `c` is exactly the set of boundary darts of `F`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

/-- **Crossers of a sector come in pairs**: if `c` is the set of darts `z` with `P z` and not
`P (α z)`, `P (σ z) ↔ P (α z)`, and `P (α x)` and `P y` hold, then an even number of passages of `c`
have exactly one end strictly between `x` and `y`. -/
theorem regionMoveLoose_even_crossers {M : CombMap.{v}} {c : List M.Dart} (hc : c.Nodup)
    (P : M.Dart → Prop) (hmem : ∀ z, z ∈ c ↔ P z ∧ ¬P (M.alpha z))
    (hP : ∀ z, P (M.sigma z) ↔ P (M.alpha z)) {x y : M.Dart} {k : ℕ} (hk0 : 0 < k)
    (hk : (M.sigma ^ k) x = y) (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y)
    (hx : P (M.alpha x)) (hy : P y) :
    Even (c.attach.countP fun p => decide (RotationBetween M x y (M.alpha p.1)) !=
      decide (RotationBetween M x y (c.next p.1 p.2))) := by
  have hS : (regionMoveLoose_sector M x k).Nodup := regionMoveLoose_sector_nodup hk hmin
  have hSm : ∀ z, z ∈ regionMoveLoose_sector M x k ↔ RotationBetween M x y z :=
    regionMoveLoose_mem_sector_iff hk0 hk hmin
  have h1 : c.attach.countP (fun p => decide (RotationBetween M x y (M.alpha p.1))) +
      c.attach.countP (fun p => decide (RotationBetween M x y (c.next p.1 p.2))) =
      2 * c.attach.countP (fun p => decide (RotationBetween M x y (M.alpha p.1)) &&
        decide (RotationBetween M x y (c.next p.1 p.2))) +
      c.attach.countP (fun p => decide (RotationBetween M x y (M.alpha p.1)) !=
        decide (RotationBetween M x y (c.next p.1 p.2))) :=
    regionMoveLoose_countP_add
      (fun p : {z // z ∈ c} => decide (RotationBetween M x y (M.alpha p.1)))
      (fun p : {z // z ∈ c} => decide (RotationBetween M x y (c.next p.1 p.2))) c.attach
  have hA1 : c.attach.countP (fun p => decide (RotationBetween M x y (M.alpha p.1))) =
      c.countP (fun z => decide (RotationBetween M x y (M.alpha z))) :=
    List.countP_attach (l := c) (p := fun z => decide (RotationBetween M x y (M.alpha z)))
  have hB1 : c.attach.countP (fun p => decide (RotationBetween M x y (c.next p.1 p.2))) =
      c.countP (fun z => decide (RotationBetween M x y z)) :=
    regionMoveLoose_countP_attach_next hc (fun z => decide (RotationBetween M x y z))
  have h2 : (regionMoveLoose_sector M x k).countP (fun z => decide (z ∈ c)) +
      (regionMoveLoose_sector M x k).countP (fun z => decide (M.alpha z ∈ c)) =
      2 * (regionMoveLoose_sector M x k).countP (fun z => decide (z ∈ c) &&
        decide (M.alpha z ∈ c)) +
      (regionMoveLoose_sector M x k).countP (fun z => decide (z ∈ c) !=
        decide (M.alpha z ∈ c)) :=
    regionMoveLoose_countP_add (fun z : M.Dart => decide (z ∈ c))
      (fun z : M.Dart => decide (M.alpha z ∈ c)) (regionMoveLoose_sector M x k)
  have hA2 : (regionMoveLoose_sector M x k).countP (fun z => decide (z ∈ c)) =
      c.countP (fun z => decide (RotationBetween M x y z)) :=
    regionMoveLoose_countP_comm hS hc (fun z => decide (z ∈ c))
      (fun z => decide (RotationBetween M x y z)) (fun _ => decide_eq_true_iff)
      (fun a => decide_eq_true_iff.trans (hSm a).symm)
  have hB2a : (regionMoveLoose_sector M x k).countP (fun z => decide (M.alpha z ∈ c)) =
      ((regionMoveLoose_sector M x k).map M.alpha).countP (fun z => decide (z ∈ c)) := by
    rw [List.countP_map]
    try rfl
  have hB2 : ((regionMoveLoose_sector M x k).map M.alpha).countP (fun z => decide (z ∈ c)) =
      c.countP (fun z => decide (RotationBetween M x y (M.alpha z))) :=
    regionMoveLoose_countP_comm (hS.map M.alpha.injective) hc (fun z => decide (z ∈ c))
      (fun z => decide (RotationBetween M x y (M.alpha z))) (fun _ => decide_eq_true_iff)
      (fun a => decide_eq_true_iff.trans ((hSm (M.alpha a)).symm.trans
        (regionMoveLoose_mem_map_involutive M.alpha_involutive).symm))
  have hN2 : (regionMoveLoose_sector M x k).countP (fun z => decide (z ∈ c) !=
        decide (M.alpha z ∈ c)) =
      (List.range' 1 (k - 1)).countP (fun i => decide (P ((M.sigma ^ i) x)) !=
        decide (P ((M.sigma ^ (i + 1)) x))) := by
    unfold regionMoveLoose_sector
    rw [List.countP_map]
    apply List.countP_congr
    intro i _
    have hs : M.sigma ((M.sigma ^ i) x) = (M.sigma ^ (i + 1)) x := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have e1 : (M.sigma ^ i) x ∈ c ↔ P ((M.sigma ^ i) x) ∧ ¬P ((M.sigma ^ (i + 1)) x) := by
      rw [hmem, ← hs, hP]
    have e2 : M.alpha ((M.sigma ^ i) x) ∈ c ↔
        P ((M.sigma ^ (i + 1)) x) ∧ ¬P ((M.sigma ^ i) x) := by
      rw [hmem, M.alpha_involutive ((M.sigma ^ i) x), ← hs, hP]
    show (decide ((M.sigma ^ i) x ∈ c) != decide (M.alpha ((M.sigma ^ i) x) ∈ c)) = true ↔
      (decide (P ((M.sigma ^ i) x)) != decide (P ((M.sigma ^ (i + 1)) x))) = true
    rw [regionMoveLoose_bne_decide e1 e2]
  have hE2 : Even ((List.range' 1 (k - 1)).countP (fun i => decide (P ((M.sigma ^ i) x)) !=
      decide (P ((M.sigma ^ (i + 1)) x)))) := by
    have hg1 : P ((M.sigma ^ 1) x) := by
      rw [pow_one, hP]
      exact hx
    have hgk : P ((M.sigma ^ (1 + (k - 1))) x) := by
      rw [show 1 + (k - 1) = k by omega, hk]
      exact hy
    apply (regionMoveLoose_even_countP_bne (fun i => decide (P ((M.sigma ^ i) x))) 1 (k - 1)).mpr
    show decide (P ((M.sigma ^ 1) x)) = decide (P ((M.sigma ^ (1 + (k - 1))) x))
    rw [decide_eq_true hg1, decide_eq_true hgk]
  rw [Nat.even_iff] at hE2 ⊢
  omega

/-- **The successor at an equal dart.** -/
theorem regionMoveLoose_next_congr {β : Type*} {l : List β} {a : β} (ha : a ∈ l) :
    ∀ (b : β) (hb : b ∈ l), b = a → l.next b hb = l.next a ha := by
  rintro b hb rfl
  rfl

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A crossing needs a second loose passage**: in a pocket with a closed boundary walk, if the
passage `d` crosses the turn at `d₀`, then some passage other than `d₀` and `d` is not tight. -/
theorem regionMoveLoose_false_of_pair (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {d₀ d : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (hd : d ∈ K.boundary.cycle)
    (hcross : ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (X.toCombMap.alpha d) ↔
      RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (K.boundary.cycle.next d hd)))
    (htight : ∀ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ → e ≠ d →
      RegionMoveCoreCloseTight K e he) : False := by
  have hxy : X.toCombMap.alpha d₀ ≠ K.boundary.cycle.next d₀ hd₀ := by
    intro h
    apply K.boundary_alpha_not_mem hd₀
    rw [h]
    exact List.next_mem hd₀
  have hv : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) =
      X.toCombMap.vertexOf (K.boundary.cycle.next d₀ hd₀) :=
    OuterPinchIsolated.rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup
      hK.1 hK.2 hd₀
  have hsc : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀)
      (K.boundary.cycle.next d₀ hd₀) := (X.toCombMap.vertexOf_eq_iff _ _).mp hv
  obtain ⟨k, hk0, hk, hmin⟩ := OuterPinchCorners.exists_firstArrival hsc hxy
  have hP : ∀ z, X.toCombMap.faceOf (X.toCombMap.sigma z) ∈ K.faces ↔
      X.toCombMap.faceOf (X.toCombMap.alpha z) ∈ K.faces := by
    intro z
    rw [← OuterPinchCornerFix.facePerm_alpha, X.toCombMap.faceOf_facePerm]
  have hx : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) ∈ K.faces := by
    rw [X.toCombMap.alpha_involutive d₀]
    exact ((K.boundary.cycle_mem_iff d₀).mp hd₀).1
  have hy : X.toCombMap.faceOf (K.boundary.cycle.next d₀ hd₀) ∈ K.faces :=
    ((K.boundary.cycle_mem_iff _).mp (List.next_mem hd₀)).1
  have hE := regionMoveLoose_even_crossers K.boundary.cycle_nodup
    (fun z => X.toCombMap.faceOf z ∈ K.faces) (fun z => K.boundary.cycle_mem_iff z) hP hk0 hk
    hmin hx hy
  have hq : ∀ b ∈ K.boundary.cycle.attach,
      (decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha b.1)) !=
        decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
          (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2))) = true ↔
        b = ⟨d, hd⟩ := by
    intro b _
    rw [regionMoveLoose_bne_true_iff]
    constructor
    · intro hb
      by_contra hbd
      by_cases hb0 : b.1 = d₀
      · apply hb
        have hxx : ¬RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
            (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha b.1) := by
          rw [hb0]
          exact regionMoveLoose_not_rotationBetween_self hk0 hk hmin
        have hyy : ¬RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
            (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2) := by
          rw [regionMoveLoose_next_congr hd₀ b.1 b.2 hb0]
          exact regionMoveLoose_not_rotationBetween_end
        exact iff_of_false hxx hyy
      · have hbd' : b.1 ≠ d := fun h => hbd (Subtype.ext h)
        exact hb (regionMoveCoreClose_not_crossed_of_tight K hd₀ b.2 (htight b.1 b.2 hb0 hbd'))
    · intro hbd
      subst hbd
      exact hcross
  have h1 : K.boundary.cycle.attach.countP (fun b =>
      decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha b.1)) !=
        decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
          (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2))) = 1 :=
    regionMoveLoose_countP_eq_one (List.nodup_attach.mpr K.boundary.cycle_nodup)
      (List.mem_attach K.boundary.cycle ⟨d, hd⟩) _ hq
  rw [h1] at hE
  exact Nat.not_even_one hE

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_even_crossers
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_next_congr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_false_of_pair
