import GroupApproximation.Higman.HNNSubextensionFiniteBaseProfinite
import GroupApproximation.Higman.FreeLampFinitePresentation
import GroupApproximation.Higman.FreeLampProfiniteEmbedding

/-!
# Finite-base free lamps are subgroup separable

For `G *_M (M × F(α))`, the base translates a `G`-state and a lamp
letter writes the pair consisting of its current right `M`-coset and its
generator.  This is the multi-stable-letter version of the faithful
free-label action for a central HNN extension.
-/

namespace GroupApproximation
namespace Higman
namespace FreeLampFiniteBaseProfinite

noncomputable section

open Monoid

variable {G α : Type} [Group G] (M : Subgroup G)

/-- The right-coset labels supplied by the central-HNN transversal. -/
abbrev Label
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  CentralHNNFreeLabel.Label M d

/-- A free-lamp label remembers both the current edge coset and the lamp
generator being read. -/
abbrev LampLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  Label M d × α

/-- State space of the free-label action. -/
abbrev Space
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  G × FreeGroup (LampLabel (M := M) (α := α) d)

/-- The chosen label of the right `M`-coset containing `x`. -/
def cosetLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) (x : G) : Label M d :=
  ((d.compl (1 : ℤˣ)).equiv x).2

/-- Base elements act by left translation on the base state. -/
def basePerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    Equiv.Perm (Space (M := M) (α := α) d) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

@[simp] theorem basePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    basePerm (M := M) (α := α) d g (x, w) = (g * x, w) := rfl

@[simp] theorem basePerm_inv_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    (basePerm (M := M) (α := α) d g)⁻¹ (x, w) = (g⁻¹ * x, w) := rfl

/-- A lamp word writes a copy of itself tagged by the current edge coset. -/
def lampPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (k : FreeGroup α) : Equiv.Perm (Space (M := M) (α := α) d) where
  toFun p :=
    (p.1, FreeGroup.map (fun i ↦ (cosetLabel M d p.1, i)) k * p.2)
  invFun p :=
    (p.1, (FreeGroup.map (fun i ↦ (cosetLabel M d p.1, i)) k)⁻¹ * p.2)
  left_inv p := by rcases p with ⟨x, w⟩; apply Prod.ext <;> simp
  right_inv p := by rcases p with ⟨x, w⟩; apply Prod.ext <;> simp

@[simp] theorem lampPerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (k : FreeGroup α) (x : G)
    (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    lampPerm (M := M) d k (x, w) =
      (x, FreeGroup.map (fun i ↦ (cosetLabel M d x, i)) k * w) := rfl

/-- The base action as a homomorphism. -/
def basePermHom
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    G →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun := basePerm (M := M) (α := α) d
  map_one' := by ext p <;> simp [basePerm]
  map_mul' g h := by ext p <;> simp [basePerm, mul_assoc]

/-- Lamp words act homomorphically because they leave the base state fixed. -/
def lampPermHom
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup α →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun := lampPerm (M := M) d
  map_one' := by
    ext p <;> rcases p with ⟨x, w⟩ <;> simp [lampPerm]
  map_mul' k l := by
    ext p <;> rcases p with ⟨x, w⟩
    · rfl
    · simp only [lampPerm_apply, Equiv.Perm.mul_apply, map_mul]
      group

/-- Left multiplication by an edge element does not change the coset label. -/
theorem cosetLabel_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (m : M) (x : G) :
    cosetLabel M d ((m : G) * x) = cosetLabel M d x := by
  exact CentralHNNFreeLabel.label_mul_left M d m x

/-- Edge translations commute with every lamp word. -/
theorem edge_commutes_lamp
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (m : M) (k : FreeGroup α) :
    Commute
      (basePerm (M := M) (α := α) d (m : G))
      (lampPerm (M := M) d k) := by
  apply Equiv.Perm.ext
  rintro ⟨x, w⟩
  apply Prod.ext
  · rfl
  · simp only [Equiv.Perm.mul_apply, basePerm_apply, lampPerm_apply]
    rw [cosetLabel_mul_left]

/-- Action of the lamp-augmented edge factor. -/
def lampFactorPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    M × FreeGroup α →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun p :=
    basePerm (M := M) (α := α) d (p.1 : G) * lampPerm (M := M) d p.2
  map_one' := by ext p <;> rcases p with ⟨x, w⟩ <;> simp
  map_mul' p q := by
    change basePerm (M := M) (α := α) d ((p.1 * q.1 : M) : G) *
        lampPerm (M := M) d (p.2 * q.2) = _
    rw [show basePerm (M := M) (α := α) d ((p.1 * q.1 : M) : G) =
        basePerm (M := M) (α := α) d (p.1 : G) *
          basePerm (M := M) (α := α) d (q.1 : G) by
          apply Equiv.Perm.ext
          rintro ⟨x, w⟩
          apply Prod.ext <;> simp [basePerm, mul_assoc],
      show lampPerm (M := M) d (p.2 * q.2) =
        lampPerm (M := M) d p.2 * lampPerm (M := M) d q.2 by
          exact map_mul (lampPermHom (M := M) d) p.2 q.2]
    calc
      basePerm (M := M) (α := α) d (p.1 : G) *
            basePerm (M := M) (α := α) d (q.1 : G) *
          (lampPerm (M := M) d p.2 * lampPerm (M := M) d q.2) =
          basePerm (M := M) (α := α) d (p.1 : G) *
            (basePerm (M := M) (α := α) d (q.1 : G) *
              lampPerm (M := M) d p.2) * lampPerm (M := M) d q.2 := by group
      _ = basePerm (M := M) (α := α) d (p.1 : G) *
            (lampPerm (M := M) d p.2 *
              basePerm (M := M) (α := α) d (q.1 : G)) *
              lampPerm (M := M) d q.2 := by
          rw [(edge_commutes_lamp M d q.1 p.2).eq]
      _ = (basePerm (M := M) (α := α) d (p.1 : G) *
            lampPerm (M := M) d p.2) *
          (basePerm (M := M) (α := α) d (q.1 : G) *
            lampPerm (M := M) d q.2) := by group

/-- The two factor actions defining the free-lamp action. -/
def factorPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) : ∀ b,
    LampFactor G M (FreeGroup α) b →*
      Equiv.Perm (Space (M := M) (α := α) d)
  | true => basePermHom (M := M) (α := α) d
  | false => lampFactorPerm (M := M) d

theorem factorPerm_comp
    (d : HNNExtension.NormalWord.TransversalPair G M M) : ∀ b,
    (factorPerm (M := M) (α := α) d b).comp
        (lampMap G M (FreeGroup α) b) =
      (basePermHom (M := M) (α := α) d).comp M.subtype := by
  intro b
  cases b with
  | false =>
      apply MonoidHom.ext
      intro m
      change basePerm (M := M) (α := α) d (m : G) *
          lampPerm (M := M) d 1 = basePerm (M := M) (α := α) d (m : G)
      rw [show lampPerm (M := M) d 1 = 1 by
        exact map_one (lampPermHom (M := M) d)]
      exact mul_one _
  | true => rfl

/-- The free-label permutation action of a free lamp. -/
def action
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeLamp G M (FreeGroup α) →*
      Equiv.Perm (Space (M := M) (α := α) d) :=
  PushoutI.lift (factorPerm (M := M) (α := α) d)
    ((basePermHom (M := M) (α := α) d).comp M.subtype)
    (factorPerm_comp (M := M) (α := α) d)

@[simp] theorem action_inAmbient
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    action (M := M) (α := α) d (inAmbient G M (FreeGroup α) g) =
      basePerm (M := M) (α := α) d g := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem action_inLamp
    (d : HNNExtension.NormalWord.TransversalPair G M M) (k : FreeGroup α) :
    action (M := M) (α := α) d (inLamp G M (FreeGroup α) k) =
      lampPerm (M := M) d k := by
  change PushoutI.lift _ _ _
      (PushoutI.of (φ := lampMap G M (FreeGroup α)) false ((1 : M), k)) = _
  rw [PushoutI.lift_of]
  change basePerm (M := M) (α := α) d 1 * lampPerm (M := M) d k = _
  rw [show basePerm (M := M) (α := α) d 1 = 1 by
    exact map_one (basePermHom (M := M) (α := α) d), one_mul]

/-! ## Stable-conjugate coordinates -/

/-- The label of the base coset, represented by the identity. -/
def oneLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) : Label M d :=
  cosetLabel M d 1

/-- A lamp generator conjugated by a chosen edge-coset representative. -/
def stableConj
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (p : LampLabel (M := M) (α := α) d) :
    FreeLamp G M (FreeGroup α) :=
  inAmbient G M (FreeGroup α) (p.1 : G)⁻¹ *
    inLamp G M (FreeGroup α) (FreeGroup.of p.2) *
      inAmbient G M (FreeGroup α) (p.1 : G)

/-- The free group on coset-tagged lamp generators maps to their stable
conjugates. -/
def stableConjLift
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (LampLabel (M := M) (α := α) d) →*
      FreeLamp G M (FreeGroup α) :=
  FreeGroup.lift (stableConj (M := M) d)

/-- A chosen stable conjugate writes its own label at the distinguished
state. -/
theorem action_stableConj_apply_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (p : LampLabel (M := M) (α := α) d)
    (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    action (M := M) (α := α) d (stableConj (M := M) d p) (1, w) =
      (1, FreeGroup.of p * w) := by
  simp only [stableConj, map_mul, map_inv, Equiv.Perm.mul_apply,
    action_inAmbient, action_inLamp, basePerm_apply, lampPerm_apply,
    basePerm_inv_apply, map_inv, mul_one]
  rw [show cosetLabel M d (p.1 : G) = p.1 by
    exact CentralHNNFreeLabel.label_self M d p.1]
  apply Prod.ext
  · simp
  · rw [FreeGroup.map.of]

/-- Stable-coordinate words act by left multiplication on the free-label
coordinate while fixing the distinguished base coordinate. -/
theorem action_stableConjLift_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (w v : FreeGroup (LampLabel (M := M) (α := α) d)) :
    action (M := M) (α := α) d (stableConjLift (M := M) d w)
        (1, v) = (1, w * v) := by
  induction w using FreeGroup.induction_on generalizing v with
  | C1 => simp
  | of p => simpa [stableConjLift] using
      action_stableConj_apply_one (M := M) d p v
  | mul x y hx hy =>
      rw [map_mul, map_mul, Equiv.Perm.mul_apply, hy]
      rw [hx]
      congr 1
      group
  | inv_of p hp =>
      rw [map_inv, map_inv]
      apply (action (M := M) (α := α) d
        (stableConjLift (M := M) d (FreeGroup.of p))).symm_apply_eq.mpr
      simpa [stableConjLift, mul_assoc] using
        (action_stableConj_apply_one (M := M) d p
          ((FreeGroup.of p)⁻¹ * v)).symm

/-- Evaluation at the distinguished state reads back a stable-conjugate word
verbatim. -/
theorem action_stableConjLift_apply_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    action (M := M) (α := α) d (stableConjLift (M := M) d w)
        (1, (1 : FreeGroup (LampLabel (M := M) (α := α) d))) =
      (1, w) := by
  simpa using action_stableConjLift_apply (M := M) d w 1

/-- Stable conjugates are freely based by `(edge coset, lamp generator)`. -/
theorem stableConjLift_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Injective (stableConjLift (M := M) (α := α) d) := by
  intro x y hxy
  have hact := congrArg (action (M := M) (α := α) d) hxy
  have hpoint := DFunLike.congr_fun hact
    ((1 : G), (1 : FreeGroup (LampLabel (M := M) (α := α) d)))
  rw [action_stableConjLift_apply_one, action_stableConjLift_apply_one] at hpoint
  exact congrArg Prod.snd hpoint

/-- A stable conjugate can be written using any representative of its right
edge coset. -/
theorem stableConj_eq_conj_of_cosetLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (s : G) (i : α) :
    stableConj (M := M) d (cosetLabel M d s, i) =
      inAmbient G M (FreeGroup α) s⁻¹ *
        inLamp G M (FreeGroup α) (FreeGroup.of i) *
          inAmbient G M (FreeGroup α) s := by
  let e := (d.compl (1 : ℤˣ)).equiv s
  have hs : (e.1 : G) * (e.2 : G) = s :=
    (d.compl (1 : ℤˣ)).equiv_fst_mul_equiv_snd s
  have hc := inLamp_commute_inAmbient G M (FreeGroup α)
    (FreeGroup.of i) e.1.property
  change inAmbient G M (FreeGroup α) (e.2 : G)⁻¹ *
      inLamp G M (FreeGroup α) (FreeGroup.of i) *
        inAmbient G M (FreeGroup α) (e.2 : G) = _
  rw [← hs, map_mul, map_inv, mul_inv_rev]
  simp only [map_mul, map_inv]
  symm
  calc
    (inAmbient G M (FreeGroup α) (e.2 : G))⁻¹ *
          (inAmbient G M (FreeGroup α) (e.1 : G))⁻¹ *
            inLamp G M (FreeGroup α) (FreeGroup.of i) *
              inAmbient G M (FreeGroup α) (e.1 : G) *
                inAmbient G M (FreeGroup α) (e.2 : G) =
        (inAmbient G M (FreeGroup α) (e.2 : G))⁻¹ *
          (inAmbient G M (FreeGroup α) (e.1 : G))⁻¹ *
            (inLamp G M (FreeGroup α) (FreeGroup.of i) *
              inAmbient G M (FreeGroup α) (e.1 : G)) *
                inAmbient G M (FreeGroup α) (e.2 : G) := by group
    _ = (inAmbient G M (FreeGroup α) (e.2 : G))⁻¹ *
          (inAmbient G M (FreeGroup α) (e.1 : G))⁻¹ *
            (inAmbient G M (FreeGroup α) (e.1 : G) *
              inLamp G M (FreeGroup α) (FreeGroup.of i)) *
                inAmbient G M (FreeGroup α) (e.2 : G) := by rw [hc.eq]
    _ = (inAmbient G M (FreeGroup α) (e.2 : G))⁻¹ *
          inLamp G M (FreeGroup α) (FreeGroup.of i) *
            inAmbient G M (FreeGroup α) (e.2 : G) := by group

/-- Conjugating a stable coordinate by a base element merely changes its
coset label. -/
theorem base_conj_stableConj
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g : G) (p : LampLabel (M := M) (α := α) d) :
    inAmbient G M (FreeGroup α) g * stableConj (M := M) d p *
        inAmbient G M (FreeGroup α) g⁻¹ =
      stableConj (M := M) d
        (cosetLabel M d ((p.1 : G) * g⁻¹), p.2) := by
  rw [stableConj_eq_conj_of_cosetLabel]
  dsimp [stableConj]
  simp only [map_mul, map_inv]
  group

/-- The stable-coordinate subgroup is normalized by the canonical base. -/
theorem base_conj_stableConjLift_mem_range
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g : G) (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    inAmbient G M (FreeGroup α) g * stableConjLift (M := M) d w *
        inAmbient G M (FreeGroup α) g⁻¹ ∈
      (stableConjLift (M := M) (α := α) d).range := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of p =>
      change inAmbient G M (FreeGroup α) g * stableConj (M := M) d p *
          inAmbient G M (FreeGroup α) g⁻¹ ∈ _
      rw [base_conj_stableConj]
      exact ⟨FreeGroup.of
        (cosetLabel M d ((p.1 : G) * g⁻¹), p.2), by
          exact FreeGroup.lift_apply_of⟩
  | mul x y hx hy =>
      rw [map_mul]
      have heq :
          inAmbient G M (FreeGroup α) g *
              (stableConjLift (M := M) d x * stableConjLift (M := M) d y) *
                inAmbient G M (FreeGroup α) g⁻¹ =
            (inAmbient G M (FreeGroup α) g * stableConjLift (M := M) d x *
                inAmbient G M (FreeGroup α) g⁻¹) *
              (inAmbient G M (FreeGroup α) g * stableConjLift (M := M) d y *
                inAmbient G M (FreeGroup α) g⁻¹) := by
          rw [map_inv]
          group
      rw [heq]
      exact Subgroup.mul_mem _ hx hy
  | inv_of p hp =>
      rw [map_inv]
      have heq :
          inAmbient G M (FreeGroup α) g *
              (stableConjLift (M := M) d (FreeGroup.of p))⁻¹ *
                inAmbient G M (FreeGroup α) g⁻¹ =
            (inAmbient G M (FreeGroup α) g *
              stableConjLift (M := M) d (FreeGroup.of p) *
                inAmbient G M (FreeGroup α) g⁻¹)⁻¹ := by
          rw [map_inv]
          group
      rw [heq]
      exact Subgroup.inv_mem _ hp

/-! ## The free kernel -/

/-- At the identity coset, stable-coordinate words are the original lamp
words. -/
theorem stableConjLift_map_oneLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (k : FreeGroup α) :
    stableConjLift (M := M) d
        (FreeGroup.map (fun i ↦ (oneLabel M d, i)) k) =
      inLamp G M (FreeGroup α) k := by
  induction k using FreeGroup.induction_on with
  | C1 => rw [map_one, map_one, map_one]
  | of i =>
      rw [FreeGroup.map.of]
      change stableConj (M := M) d (cosetLabel M d 1, i) = _
      simpa using stableConj_eq_conj_of_cosetLabel (M := M) d 1 i
  | mul x y hx hy =>
      rw [map_mul, map_mul, map_mul, hx, hy]
  | inv_of i hi =>
      rw [map_inv, map_inv, map_inv, hi]

/-- Multiplication in the lamp factor splits into its edge and lamp parts. -/
theorem rightFactor_eq_ambient_mul_lamp
    (l : M) (k : FreeGroup α) :
    PushoutI.of (φ := lampMap G M (FreeGroup α)) false (l, k) =
      inAmbient G M (FreeGroup α) (l : G) *
        inLamp G M (FreeGroup α) k := by
  have hedge :
      PushoutI.of (φ := lampMap G M (FreeGroup α)) false (l, 1) =
        inAmbient G M (FreeGroup α) (l : G) := by
    exact (PushoutI.of_apply_eq_base
      (lampMap G M (FreeGroup α)) false l).trans
      (PushoutI.of_apply_eq_base
        (lampMap G M (FreeGroup α)) true l).symm
  calc
    PushoutI.of (φ := lampMap G M (FreeGroup α)) false (l, k) =
        PushoutI.of (φ := lampMap G M (FreeGroup α)) false
          ((l, 1) * ((1 : M), k)) := by
            congr 1
            apply Prod.ext
            · exact (mul_one l).symm
            · exact (one_mul k).symm
    _ = PushoutI.of (φ := lampMap G M (FreeGroup α)) false (l, 1) *
          PushoutI.of (φ := lampMap G M (FreeGroup α)) false ((1 : M), k) :=
      map_mul _ _ _
    _ = inAmbient G M (FreeGroup α) (l : G) *
          inLamp G M (FreeGroup α) k := by rw [hedge]; rfl

/-- Every free-lamp element is a stable-coordinate word followed by a base
element. -/
theorem exists_stableConjLift_mul_inAmbient
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (z : FreeLamp G M (FreeGroup α)) :
    ∃ w g, z = stableConjLift (M := M) d w *
      inAmbient G M (FreeGroup α) g := by
  induction z using PushoutI.induction_on with
  | of b p =>
      cases b with
      | false =>
          change M × FreeGroup α at p
          refine ⟨FreeGroup.map (fun i ↦ (oneLabel M d, i)) p.2,
            (p.1 : G), ?_⟩
          rw [stableConjLift_map_oneLabel]
          rw [rightFactor_eq_ambient_mul_lamp]
          rw [(inLamp_commute_inAmbient G M (FreeGroup α)
            p.2 p.1.property).eq]
      | true =>
          exact ⟨1, p, by simp⟩
  | base m =>
      refine ⟨1, (m : G), ?_⟩
      rw [map_one, one_mul]
      exact (PushoutI.of_apply_eq_base
        (lampMap G M (FreeGroup α)) true m).symm
  | mul x y hx hy =>
      obtain ⟨wx, gx, hx⟩ := hx
      obtain ⟨wy, gy, hy⟩ := hy
      obtain ⟨wy', hwy'⟩ :=
        base_conj_stableConjLift_mem_range (M := M) d gx wy
      refine ⟨wx * wy', gx * gy, ?_⟩
      rw [map_mul, map_mul, hx, hy, hwy']
      simp only [map_inv]
      group

@[simp] theorem baseRet_inLamp (k : FreeGroup α) :
    FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)
      (inLamp G M (FreeGroup α) k) = 1 := by
  change PushoutI.lift _ _ _
      (PushoutI.of (φ := lampMap G M (FreeGroup α)) false ((1 : M), k)) = 1
  rw [PushoutI.lift_of]
  rfl

@[simp] theorem baseRet_stableConj
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (p : LampLabel (M := M) (α := α) d) :
    FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)
      (stableConj (M := M) d p) = 1 := by
  simp only [stableConj, map_mul, map_inv,
    FreeLampProfiniteEmbedding.baseRet_inAmbient, baseRet_inLamp]
  group

theorem baseRet_comp_stableConjLift
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).comp
        (stableConjLift (M := M) (α := α) d) = 1 := by
  refine FreeGroup.ext_hom _ _ fun p => ?_
  simp [stableConjLift]

/-- The stable-coordinate subgroup is exactly the kernel of the canonical
base retraction. -/
theorem range_stableConjLift_eq_ker_baseRet
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    (stableConjLift (M := M) (α := α) d).range =
      (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      baseRet_comp_stableConjLift]
    rfl
  · intro z hz
    obtain ⟨w, g, hdecomp⟩ :=
      exists_stableConjLift_mul_inAmbient (M := M) d z
    have hz' := hz
    rw [MonoidHom.mem_ker, hdecomp, map_mul,
      ← MonoidHom.comp_apply, baseRet_comp_stableConjLift,
      FreeLampProfiniteEmbedding.baseRet_inAmbient] at hz'
    have hg : g = 1 := by simpa using hz'
    subst g
    rw [map_one, mul_one] at hdecomp
    exact ⟨w, hdecomp.symm⟩

/-- The free stable-coordinate basis, restricted to the retraction kernel. -/
def kernelLift
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (LampLabel (M := M) (α := α) d) →*
      (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker :=
  (stableConjLift (M := M) (α := α) d).codRestrict _ fun w ↦ by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      baseRet_comp_stableConjLift]
    rfl

theorem kernelLift_bijective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Bijective (kernelLift (M := M) (α := α) d) := by
  constructor
  · intro x y hxy
    apply stableConjLift_injective (M := M) (α := α) d
    exact Subtype.ext_iff.mp hxy
  · rintro ⟨z, hz⟩
    have hzrange : z ∈ (stableConjLift (M := M) (α := α) d).range := by
      rw [range_stableConjLift_eq_ker_baseRet]
      exact hz
    obtain ⟨w, hw⟩ := hzrange
    exact ⟨w, Subtype.ext hw⟩

/-- The base-retraction kernel is intrinsically a free group. -/
noncomputable def kernelEquiv
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (LampLabel (M := M) (α := α) d) ≃*
      (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker :=
  MulEquiv.ofBijective (kernelLift (M := M) (α := α) d)
    (kernelLift_bijective (M := M) (α := α) d)

theorem kernelEquiv_comp_subtype
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    ((FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker.subtype).comp
        (kernelEquiv (M := M) (α := α) d).toMonoidHom =
      stableConjLift (M := M) (α := α) d := by
  ext w
  rfl

instance kernel_finiteIndex [Finite G] :
    (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker.FiniteIndex := by
  exact finiteIndex_comap_of_normal
    (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α))
    (⊥ : Subgroup G)

/-! ## Faithfulness and subgroup separability -/

/-- An element acting trivially is the identity. -/
theorem eq_one_of_action_eq_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {z : FreeLamp G M (FreeGroup α)}
    (hz : action (M := M) (α := α) d z = 1) : z = 1 := by
  obtain ⟨w, g, hdecomp⟩ :=
    exists_stableConjLift_mul_inAmbient (M := M) d z
  have happ := DFunLike.congr_fun hz
    (g⁻¹, (1 : FreeGroup (LampLabel (M := M) (α := α) d)))
  rw [hdecomp, map_mul, Equiv.Perm.mul_apply, action_inAmbient,
    basePerm_apply, mul_inv_cancel,
    action_stableConjLift_apply_one] at happ
  have hg_inv : g⁻¹ = 1 := by
    simpa using (congrArg Prod.fst happ).symm
  have hg : g = 1 := inv_eq_one.mp hg_inv
  have hw : w = 1 := by simpa using congrArg Prod.snd happ
  subst g
  subst w
  simpa using hdecomp

/-- The free-label action of a free lamp is faithful for every base group. -/
theorem action_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Injective (action (M := M) (α := α) d) := by
  refine (MonoidHom.ker_eq_bot_iff (action (M := M) (α := α) d)).mp ?_
  apply le_antisymm
  · intro z hz
    have hz1 := eq_one_of_action_eq_one (M := M) (α := α) d hz
    simp [hz1]
  · exact bot_le

/-- **A free lamp over a finite base is LERF.**  Its canonical base
retraction has free finite-index kernel, so Hall's theorem promotes through
the finite extension. -/
theorem profiniteClosure_eq_of_fg [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (H : Subgroup (FreeLamp G M (FreeGroup α))) (hH : H.FG) :
    profiniteClosure H = H := by
  let K : Subgroup (FreeLamp G M (FreeGroup α)) :=
    (FreeLampProfiniteEmbedding.baseRet G M (FreeGroup α)).ker
  let e := kernelEquiv (M := M) (α := α) d
  apply profiniteClosure_eq_of_normal_finiteIndex_lerf K ?_ H hH
  intro L hL
  let P : Subgroup (FreeGroup (LampLabel (M := M) (α := α) d)) :=
    L.map e.symm.toMonoidHom
  have hPfg : P.FG := Higman.fg_map hL e.symm.toMonoidHom
  have hPclosed : profiniteClosure P = P :=
    FreeGroupHall.profiniteClosure_eq_of_fg P hPfg
  haveI : Group.ResiduallyFinite K := residuallyFinite_of_mulEquiv e.symm
  have hmapped := profiniteClosure_map_eq_of_split_closed e.toMonoidHom
    e.symm.toMonoidHom (by ext w; simp) P hPclosed
  have hPe : P.map e.toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨p, hp, hpx⟩
      obtain ⟨l, hl, hlp⟩ := hp
      subst p
      have hlx : l = x := by simpa using hpx
      rwa [hlx] at hl
    · intro hx
      refine ⟨e.symm x, ⟨x, hx, rfl⟩, ?_⟩
      simp
  rwa [hPe] at hmapped

/-- LERF transported to a lamp group presented as a free group. -/
theorem profiniteClosure_eq_of_fg_of_lampEquiv
    {K : Type} [Group K] [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (e : K ≃* FreeGroup α)
    (H : Subgroup (FreeLamp G M K)) (hH : H.FG) :
    profiniteClosure H = H := by
  let E : FreeLamp G M K ≃* FreeLamp G M (FreeGroup α) :=
    FreeLampFinitePresentation.freeLampEquivOfLampEquiv G M e
  let P : Subgroup (FreeLamp G M (FreeGroup α)) := H.map E.toMonoidHom
  have hPfg : P.FG := Higman.fg_map hH E.toMonoidHom
  have hPclosed : profiniteClosure P = P :=
    profiniteClosure_eq_of_fg (M := M) d P hPfg
  apply le_antisymm
  · intro x hx
    have hex : E x ∈ profiniteClosure P := by
      intro Q _ _ q
      obtain ⟨h, hh, heq⟩ := hx Q (q.comp E.toMonoidHom)
      refine ⟨E h, ⟨h, hh, rfl⟩, ?_⟩
      change q (E.toMonoidHom h) = q (E.toMonoidHom x)
      simpa only [MonoidHom.comp_apply] using heq
    rw [hPclosed] at hex
    obtain ⟨h, hh, heq⟩ := hex
    have : h = x := E.injective heq
    rwa [← this]
  · exact le_profiniteClosure H

end

end FreeLampFiniteBaseProfinite
end Higman
end GroupApproximation
