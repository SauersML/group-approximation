import GroupApproximation.Higman.HNNCentralizer
import GroupApproximation.Sofic.FreeLampReduction

/-!
# A free lamp of rank two is an iterated central HNN extension

For a subgroup `L ≤ G`, the amalgam

`G *_L (L × FreeGroup (Fin 2))`

is the group obtained from `G` by adjoining two stable letters, each of which
centralizes `L`.  This file proves that statement directly from the universal
properties of `PushoutI`, `FreeGroup`, and `HNNExtension`.  Consequently the
amalgam is finitely presented whenever `G` is finitely presented and `L` is
finitely generated; no finite-presentation hypothesis on `L` is needed.
-/

namespace GroupApproximation
namespace FreeLampFinitePresentation

open Monoid HNNExtension

variable (G : Type) [Group G] (L : Subgroup G)

/-- The first central HNN extension. -/
abbrev Stage1 : Type := Higman.CentHNN L

/-- The copy of `L` in the first central HNN extension. -/
def stage1Sub : Subgroup (Stage1 G L) :=
  L.map (HNNExtension.of : G →* Stage1 G L)

/-- The second central HNN extension. -/
abbrev Stage2 : Type := Higman.CentHNN (stage1Sub G L)

/-- The canonical copy of `G` in the second stage. -/
def baseToStage2 : G →* Stage2 G L :=
  (HNNExtension.of : Stage1 G L →* Stage2 G L).comp
    (HNNExtension.of : G →* Stage1 G L)

/-- The two stable letters, indexed by `Fin 2`. -/
def stableGen : Fin 2 → Stage2 G L
  | 0 => HNNExtension.of (HNNExtension.t : Stage1 G L)
  | 1 => HNNExtension.t

/-- The homomorphism from the rank-two free group to the two stable letters. -/
def freeToStage2 : FreeGroup (Fin 2) →* Stage2 G L :=
  FreeGroup.lift (stableGen G L)

theorem stableGen_commute_base (i : Fin 2) {g : G} (hg : g ∈ L) :
    Commute (stableGen G L i) (baseToStage2 G L g) := by
  fin_cases i
  · exact (Higman.commute_t_of_iff L g).2 hg |>.map
      (HNNExtension.of : Stage1 G L →* Stage2 G L)
  · exact (Higman.commute_t_of_iff (stage1Sub G L)
      ((HNNExtension.of : G →* Stage1 G L) g)).2 ⟨g, hg, rfl⟩

theorem freeToStage2_commute_base (w : FreeGroup (Fin 2)) {g : G} (hg : g ∈ L) :
    Commute (freeToStage2 G L w) (baseToStage2 G L g) := by
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_left _
  | of i => simpa only [freeToStage2, FreeGroup.lift_apply_of] using
      stableGen_commute_base G L i hg
  | mul x y hx hy => simpa only [map_mul] using hx.mul_left hy
  | inv_of i hi => simpa only [map_inv] using hi.inv_left

/-- The right vertex `L × F₂` maps to the iterated HNN extension. -/
def lampFactorToStage2 : L × FreeGroup (Fin 2) →* Stage2 G L where
  toFun p := baseToStage2 G L (p.1 : G) * freeToStage2 G L p.2
  map_one' := by simp
  map_mul' p q := by
    have hc := freeToStage2_commute_base G L p.2 q.1.property
    change baseToStage2 G L (((p.1 * q.1 : L) : L) : G) *
        freeToStage2 G L (p.2 * q.2) =
      (baseToStage2 G L (p.1 : G) * freeToStage2 G L p.2) *
        (baseToStage2 G L (q.1 : G) * freeToStage2 G L q.2)
    rw [show (((p.1 * q.1 : L) : L) : G) = (p.1 : G) * (q.1 : G) from rfl,
      map_mul, map_mul]
    calc
      baseToStage2 G L (p.1 : G) * baseToStage2 G L (q.1 : G) *
          (freeToStage2 G L p.2 * freeToStage2 G L q.2) =
        baseToStage2 G L (p.1 : G) *
          (baseToStage2 G L (q.1 : G) * freeToStage2 G L p.2) *
            freeToStage2 G L q.2 := by group
      _ = baseToStage2 G L (p.1 : G) *
          (freeToStage2 G L p.2 * baseToStage2 G L (q.1 : G)) *
            freeToStage2 G L q.2 := by rw [hc.eq]
      _ = baseToStage2 G L (p.1 : G) * freeToStage2 G L p.2 *
          (baseToStage2 G L (q.1 : G) * freeToStage2 G L q.2) := by group

/-- The two factor maps from the free-lamp pushout into the iterated HNN
extension. -/
def toStage2Factors : ∀ b,
    LampFactor G L (FreeGroup (Fin 2)) b →* Stage2 G L
  | true => baseToStage2 G L
  | false => lampFactorToStage2 G L

theorem toStage2Factors_comp : ∀ b,
    (toStage2Factors G L b).comp (lampMap G L (FreeGroup (Fin 2)) b) =
      (baseToStage2 G L).comp L.subtype := by
  intro b
  cases b
  · ext l
    change baseToStage2 G L (l : G) * freeToStage2 G L 1 =
      baseToStage2 G L (l : G)
    simp
  · rfl

/-- The canonical map from the free-lamp amalgam to the two-stage HNN tower. -/
def toStage2 : FreeLamp G L (FreeGroup (Fin 2)) →* Stage2 G L :=
  PushoutI.lift (toStage2Factors G L) ((baseToStage2 G L).comp L.subtype)
    (toStage2Factors_comp G L)

@[simp] theorem toStage2_inAmbient (g : G) :
    toStage2 G L (inAmbient G L (FreeGroup (Fin 2)) g) = baseToStage2 G L g := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem freeToStage2_of (i : Fin 2) :
    freeToStage2 G L (FreeGroup.of i) = stableGen G L i := by
  simp [freeToStage2]

@[simp] theorem toStage2_inLamp_of (i : Fin 2) :
    toStage2 G L (inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of i)) =
      stableGen G L i := by
  change PushoutI.lift _ _ _
      (PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false
        ((1 : L), FreeGroup.of i)) = _
  rw [PushoutI.lift_of]
  change baseToStage2 G L (1 : G) * freeToStage2 G L (FreeGroup.of i) = _
  simp

/-! ## The inverse map -/

/-- The first HNN stage maps back by sending its stable letter to lamp zero. -/
def stage1ToLamp : Stage1 G L →* FreeLamp G L (FreeGroup (Fin 2)) :=
  HNNExtension.lift (inAmbient G L (FreeGroup (Fin 2)))
    (inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 0)) (fun l => by
      exact (inLamp_commute_inAmbient G L (FreeGroup (Fin 2))
        (FreeGroup.of 0) l.property).eq)

@[simp] theorem stage1ToLamp_of (g : G) :
    stage1ToLamp G L (HNNExtension.of g) =
      inAmbient G L (FreeGroup (Fin 2)) g := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem stage1ToLamp_t :
    stage1ToLamp G L (HNNExtension.t : Stage1 G L) =
      inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 0) := by
  exact HNNExtension.lift_t _ _ _

/-- The second HNN stage maps back by sending its stable letter to lamp one. -/
def fromStage2 : Stage2 G L →* FreeLamp G L (FreeGroup (Fin 2)) :=
  HNNExtension.lift (stage1ToLamp G L)
    (inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 1)) (fun l => by
      obtain ⟨g, hg, hgl⟩ := l.property
      have hcoe : (l : Stage1 G L) = HNNExtension.of g := hgl.symm
      rw [show ((MulEquiv.refl (stage1Sub G L)) l : stage1Sub G L) = l from rfl,
        hcoe, stage1ToLamp_of]
      exact (inLamp_commute_inAmbient G L (FreeGroup (Fin 2))
        (FreeGroup.of 1) hg).eq)

@[simp] theorem fromStage2_of (x : Stage1 G L) :
    fromStage2 G L (HNNExtension.of x) = stage1ToLamp G L x := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem fromStage2_t :
    fromStage2 G L (HNNExtension.t : Stage2 G L) =
      inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 1) := by
  exact HNNExtension.lift_t _ _ _

/-- Multiplication in the right vertex splits into its edge and lamp parts. -/
theorem rightFactor_eq_ambient_mul_lamp (l : L) (w : FreeGroup (Fin 2)) :
    PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false (l, w) =
      inAmbient G L (FreeGroup (Fin 2)) (l : G) *
        inLamp G L (FreeGroup (Fin 2)) w := by
  have hedge :
      PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false (l, 1) =
        inAmbient G L (FreeGroup (Fin 2)) (l : G) := by
    exact (PushoutI.of_apply_eq_base
      (lampMap G L (FreeGroup (Fin 2))) false l).trans
      (PushoutI.of_apply_eq_base
        (lampMap G L (FreeGroup (Fin 2))) true l).symm
  calc
    PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false (l, w) =
        PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false
          ((l, 1) * ((1 : L), w)) := by
            congr 1
            apply Prod.ext
            · exact (mul_one l).symm
            · exact (one_mul w).symm
    _ = PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false (l, 1) *
          PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false ((1 : L), w) :=
        map_mul _ _ _
    _ = inAmbient G L (FreeGroup (Fin 2)) (l : G) *
          inLamp G L (FreeGroup (Fin 2)) w := by rw [hedge]; rfl

theorem fromStage2_comp_toStage2 :
    (fromStage2 G L).comp (toStage2 G L) =
      MonoidHom.id (FreeLamp G L (FreeGroup (Fin 2))) := by
  apply PushoutI.hom_ext_nonempty
  intro b
  cases b
  · ext p
    rcases p with ⟨l, w⟩
    simp only [MonoidHom.comp_apply]
    change fromStage2 G L
        (baseToStage2 G L (l : G) * freeToStage2 G L w) = _
    rw [map_mul, baseToStage2, MonoidHom.comp_apply, fromStage2_of,
      stage1ToLamp_of, rightFactor_eq_ambient_mul_lamp]
    congr 1
    induction w using FreeGroup.induction_on with
    | C1 => exact (map_one
        (PushoutI.of (φ := lampMap G L (FreeGroup (Fin 2))) false)).symm
    | of i => fin_cases i <;> simp [freeToStage2, stableGen]
    | mul x y hx hy =>
        simpa only [map_mul] using congrArg₂ (fun a b => a * b) hx hy
    | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  · ext g
    change fromStage2 G L
      (toStage2 G L (inAmbient G L (FreeGroup (Fin 2)) g)) =
        inAmbient G L (FreeGroup (Fin 2)) g
    rw [toStage2_inAmbient, baseToStage2, MonoidHom.comp_apply,
      fromStage2_of, stage1ToLamp_of]

theorem toStage2_comp_fromStage2 :
    (toStage2 G L).comp (fromStage2 G L) = MonoidHom.id (Stage2 G L) := by
  apply HNNExtension.hom_ext
  · apply HNNExtension.hom_ext
    · ext g
      change toStage2 G L (inAmbient G L (FreeGroup (Fin 2)) g) =
        baseToStage2 G L g
      exact toStage2_inAmbient G L g
    · change toStage2 G L
        (inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 0)) =
          stableGen G L 0
      exact toStage2_inLamp_of G L 0
  · change toStage2 G L
      (inLamp G L (FreeGroup (Fin 2)) (FreeGroup.of 1)) = stableGen G L 1
    exact toStage2_inLamp_of G L 1

/-- **The rank-two free-lamp amalgam is exactly two central HNN extensions.** -/
def freeLampEquivStage2 :
    FreeLamp G L (FreeGroup (Fin 2)) ≃* Stage2 G L where
  toFun := toStage2 G L
  invFun := fromStage2 G L
  left_inv x := congrArg (fun f => f x) (fromStage2_comp_toStage2 G L)
  right_inv x := congrArg (fun f => f x) (toStage2_comp_fromStage2 G L)
  map_mul' := map_mul _

/-! ## Finite presentation -/

/-- **A rank-two free-lamp amalgam is finitely presented over a finitely
presented vertex and a finitely generated edge.** -/
theorem isFinitelyPresented_freeLamp [Group.IsFinitelyPresented G] (hL : L.FG) :
    Group.IsFinitelyPresented (FreeLamp G L (FreeGroup (Fin 2))) := by
  letI : Group.IsFinitelyPresented (Stage1 G L) :=
    Higman.isFinitelyPresented_centHNN L hL
  have hmap : (stage1Sub G L).FG := Higman.fg_map hL HNNExtension.of
  letI : Group.IsFinitelyPresented (Stage2 G L) :=
    Higman.isFinitelyPresented_centHNN (stage1Sub G L) hmap
  exact Group.IsFinitelyPresented.equiv (freeLampEquivStage2 G L).symm

/-! ## Transporting the lamp group -/

section Transport

variable {K K' : Type} [Group K] [Group K']

/-- An equivalence of lamp groups acts on the right vertex and fixes its edge
coordinate. -/
def lampFactorMap (e : K ≃* K') : L × K →* L × K' where
  toFun p := (p.1, e p.2)
  map_one' := by simp
  map_mul' p q := by ext <;> simp

/-- Factorwise map induced by changing the lamp group. -/
def lampChangeFactors (e : K ≃* K') : ∀ b,
    LampFactor G L K b →* LampFactor G L K' b
  | true => MonoidHom.id G
  | false => lampFactorMap G L e

theorem lampChangeFactors_comp (e : K ≃* K') : ∀ b,
    (lampChangeFactors G L e b).comp (lampMap G L K b) = lampMap G L K' b := by
  intro b
  cases b
  · ext l
    change (l, e (1 : K)) = (l, (1 : K'))
    simp
  · rfl

/-- A lamp-group equivalence induces a homomorphism of free-lamp amalgams. -/
def freeLampMap (e : K ≃* K') : FreeLamp G L K →* FreeLamp G L K' :=
  PushoutI.lift
    (fun b => (PushoutI.of (φ := lampMap G L K') b).comp
      (lampChangeFactors G L e b))
    (PushoutI.base (lampMap G L K')) (fun b => by
      rw [MonoidHom.comp_assoc, lampChangeFactors_comp]
      ext l
      exact PushoutI.of_apply_eq_base (lampMap G L K') b l)

@[simp] theorem freeLampMap_inAmbient (e : K ≃* K') (g : G) :
    freeLampMap G L e (inAmbient G L K g) = inAmbient G L K' g := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem freeLampMap_inLamp (e : K ≃* K') (k : K) :
    freeLampMap G L e (inLamp G L K k) = inLamp G L K' (e k) := by
  change PushoutI.lift _ _ _
      (PushoutI.of (φ := lampMap G L K) false ((1 : L), k)) = _
  rw [PushoutI.lift_of]
  rfl

theorem freeLampMap_symm_comp (e : K ≃* K') :
    (freeLampMap G L e.symm).comp (freeLampMap G L e) =
      MonoidHom.id (FreeLamp G L K) := by
  apply PushoutI.hom_ext_nonempty
  intro b
  cases b
  · ext p
    rcases p with ⟨l, k⟩
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    change freeLampMap G L e.symm
      (PushoutI.of (φ := lampMap G L K') false (l, e k)) =
        PushoutI.of (φ := lampMap G L K) false (l, k)
    rw [freeLampMap, PushoutI.lift_of]
    change PushoutI.of (φ := lampMap G L K) false (l, e.symm (e k)) = _
    rw [e.symm_apply_apply]
  · ext g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    change freeLampMap G L e.symm
      (freeLampMap G L e (inAmbient G L K g)) = inAmbient G L K g
    rw [freeLampMap_inAmbient, freeLampMap_inAmbient]

theorem freeLampMap_comp_symm (e : K ≃* K') :
    (freeLampMap G L e).comp (freeLampMap G L e.symm) =
      MonoidHom.id (FreeLamp G L K') := by
  simpa using freeLampMap_symm_comp G L e.symm

/-- **Free-lamp amalgams depend on the lamp group only up to equivalence.** -/
def freeLampEquivOfLampEquiv (e : K ≃* K') :
    FreeLamp G L K ≃* FreeLamp G L K' where
  toFun := freeLampMap G L e
  invFun := freeLampMap G L e.symm
  left_inv x := congrArg (fun f => f x) (freeLampMap_symm_comp G L e)
  right_inv x := congrArg (fun f => f x) (freeLampMap_comp_symm G L e)
  map_mul' := map_mul _

/-- Finite presentation transported across an arbitrary rank-two lamp
equivalence. -/
theorem isFinitelyPresented_freeLamp_of_equiv [Group.IsFinitelyPresented G]
    (hL : L.FG) (e : K ≃* FreeGroup (Fin 2)) :
    Group.IsFinitelyPresented (FreeLamp G L K) := by
  have hfp := isFinitelyPresented_freeLamp G L hL
  exact Group.IsFinitelyPresented.equiv (freeLampEquivOfLampEquiv G L e).symm

end Transport

end FreeLampFinitePresentation
end GroupApproximation
