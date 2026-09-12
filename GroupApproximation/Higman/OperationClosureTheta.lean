import GroupApproximation.Higman.OperationClosureRho
import GroupApproximation.Higman.OmegaClosure

/-!
# Higman's operation `θ`, and the single statement it reduces to

`θ B = {f | ∃ g ∈ B, ∀ i, f i = g (2 * i)}` --- read off the even
coordinates.  Unlike `ρ`, the index map `i ↦ 2 * i` is order-*preserving*, so
it commutes with the sort that defines `elt` and is induced by an
endomorphism of `F₃`,

    dblAut : a ↦ a,  b ↦ b,  c ↦ c²,

which sends the `i`-th row to the `2i`-th (`dblAut_rowElt`) and hence the
coding of `f` to the coding of `f` spread out over the even coordinates
(`aElt_dblSeq`).  The endomorphism is *not* surjective, so `Benign.congr` does
not apply; what applies instead is `Benign.comap`, and for that the
endomorphism has to be injective.  That is `dblAut_injective`, proved here by
the same device `Higman.RowBasis` and `Higman.ConjugateBasis` use for their
free bases: an action on words-with-a-bit in which `c` moves the bit and
every second `c` writes a letter, so a doubled word can be read back.

What comes out is

    ASub (θ B) = (ASub (κ B)).comap dblAut                  (`ASub_thetaOp`)

where `κ B = evenOp B` is `B` with the odd coordinates set to zero.  So `θ`
costs exactly one further closure property:

> **if `A_B` is benign then so is `A_{κ B}`**, where `κ` kills the odd
> coordinates.

`κ` is of the same species as Higman's `ζ` and `π` --- an operation that
touches a set of coordinates and leaves the rest alone --- and is the natural
place for `θ` to meet them.  Nothing about the doubling, the sort or the
coding is left in it.  `evenOp_eq_inter` makes the meeting exact: `κ B` is the
agreement operation on the even coordinates, intersected with the *fixed* set
of sequences vanishing on the odd ones, so `κ` costs the `ζ`/`π` machinery
plus one benignness statement with no `B` in it.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  Doubling the index -/

/-- Doubling, as an embedding of the index set. -/
def dblEmb : ℤ ↪ ℤ where
  toFun i := 2 * i
  inj' x y h := by
    have h' : 2 * x = 2 * y := h
    omega

@[simp] theorem dblEmb_apply (i : ℤ) : dblEmb i = 2 * i := rfl

/-- Doubling is order-preserving, so it commutes with the sort. -/
theorem sort_map_dbl (s : Finset ℤ) :
    (s.map dblEmb).sort (· ≤ ·) = (s.sort (· ≤ ·)).map (fun i : ℤ => 2 * i) := by
  symm
  exact Finset.map_sort (s := s) (r := ((· ≤ ·) : ℤ → ℤ → Prop))
    (r' := ((· ≤ ·) : ℤ → ℤ → Prop)) (f := dblEmb)
    (fun x _ y _ => by
      show x ≤ y ↔ 2 * x ≤ 2 * y
      omega)

/-- The sequence `f`, moved onto the even coordinates. -/
noncomputable def dblSeq (f : E) : E := Finsupp.embDomain dblEmb f

@[simp] theorem dblSeq_two_mul (f : E) (i : ℤ) : dblSeq f (2 * i) = f i :=
  Finsupp.embDomain_apply_self dblEmb f i

theorem dblSeq_support (f : E) : (dblSeq f).support = f.support.map dblEmb :=
  Finsupp.support_embDomain dblEmb f

theorem dblSeq_of_notMem_range (f : E) (i : ℤ) (h : ∀ k : ℤ, i ≠ 2 * k) :
    dblSeq f i = 0 := by
  unfold dblSeq
  refine Finsupp.embDomain_notin_range _ _ _ ?_
  rintro ⟨k, hk⟩
  exact h k hk.symm

/-- The doubling on the free group of the index set. -/
def dblFree : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => FreeGroup.of (2 * i))

@[simp] theorem dblFree_of (i : ℤ) :
    dblFree (FreeGroup.of i) = FreeGroup.of (2 * i) := by
  unfold dblFree
  rw [FreeGroup.lift_apply_of]

/-- **The coding intertwines the two doublings.** -/
theorem elt_dblSeq (f : E) : elt (dblSeq f) = dblFree (elt f) := by
  unfold elt
  rw [dblSeq_support, sort_map_dbl, List.map_map, map_list_prod, List.map_map]
  refine congrArg List.prod ?_
  refine List.map_congr_left fun j _ => ?_
  show FreeGroup.of (2 * j) ^ dblSeq f (2 * j) = dblFree (FreeGroup.of j ^ f j)
  rw [map_zpow, dblFree_of, dblSeq_two_mul]

/-! ## 2.  The endomorphism of `F₃` -/

/-- The endomorphism realizing the doubling. -/
def dblAut : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then a else if i = 1 then b else c ^ (2 : ℤ))

@[simp] theorem dblAut_a : dblAut a = a := by
  unfold dblAut a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem dblAut_b : dblAut b = b := by
  unfold dblAut b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem dblAut_c : dblAut c = c ^ (2 : ℤ) := by
  unfold dblAut c
  rw [FreeGroup.lift_apply_of]
  simp

/-- **The endomorphism doubles the row index.** -/
theorem dblAut_rowElt (i : ℤ) : dblAut (rowElt i) = rowElt (2 * i) := by
  unfold rowElt
  rw [map_mul, map_mul, map_zpow, map_zpow, dblAut_b, dblAut_c, ← zpow_mul, ← zpow_mul]
  have h : (2 : ℤ) * -i = -(2 * i) := by ring
  rw [h]

theorem dblAut_comp_rowHom : dblAut.comp rowHom = rowHom.comp dblFree := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show dblAut (rowHom (FreeGroup.of i)) = rowHom (dblFree (FreeGroup.of i))
  rw [rowHom_of, dblFree_of, rowHom_of, dblAut_rowElt]

theorem bElt_dblSeq (f : E) : bElt (dblSeq f) = dblAut (bElt f) := by
  unfold bElt
  rw [elt_dblSeq]
  exact (congrArg (fun g : FreeGroup ℤ →* F₃ => g (elt f)) dblAut_comp_rowHom).symm

theorem aElt_dblSeq (f : E) : aElt (dblSeq f) = dblAut (aElt f) := by
  unfold aElt
  rw [bElt_dblSeq, map_mul, map_mul, map_inv, dblAut_a]

/-! ## 3.  The doubling is injective

The subgroup generated by `a`, `b` and `c²` is free on them.  The proof is the
device of `Higman.RowBasis`: act on words carrying one extra bit, let `c` flip
the bit and let every *second* `c` prepend the letter `c`, so that the action
of `dblAut W` on the empty word returns `W`. -/

/-- Words with a bit recording whether a `c` has been seen but not yet
paired. -/
abbrev DSlice : Type := F₃ × Bool

/-- Prepending `a`. -/
def aDPerm : Equiv.Perm DSlice where
  toFun p := (a * p.1, p.2)
  invFun p := (a⁻¹ * p.1, p.2)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Prepending `b`. -/
def bDPerm : Equiv.Perm DSlice where
  toFun p := (b * p.1, p.2)
  invFun p := (b⁻¹ * p.1, p.2)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Flipping the bit, and prepending `c` on every second flip. -/
def cDPerm : Equiv.Perm DSlice where
  toFun p := if p.2 then (c * p.1, false) else (p.1, true)
  invFun p := if p.2 then (p.1, false) else (c⁻¹ * p.1, true)
  left_inv := by rintro ⟨w, u⟩; cases u <;> simp
  right_inv := by rintro ⟨w, u⟩; cases u <;> simp

/-- The action that reads a doubled word back. -/
def dblAct : F₃ →* Equiv.Perm DSlice :=
  FreeGroup.lift
    (fun i : Fin 3 => if i = 0 then aDPerm else if i = 1 then bDPerm else cDPerm)

@[simp] theorem dblAct_a : dblAct a = aDPerm := by
  unfold dblAct a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem dblAct_b : dblAct b = bDPerm := by
  unfold dblAct b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem dblAct_c : dblAct c = cDPerm := by
  unfold dblAct c
  rw [FreeGroup.lift_apply_of]
  simp

/-- **The action reads the doubled word back.** -/
theorem dblAct_dblAut (W : F₃) :
    ∀ w : F₃, dblAct (dblAut W) (w, false) = (W * w, false) := by
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · intro w
    rw [map_one, map_one, one_mul]
    rfl
  · intro i w
    fin_cases i
    · show dblAct (dblAut a) (w, false) = (a * w, false)
      rw [dblAut_a, dblAct_a]
      rfl
    · show dblAct (dblAut b) (w, false) = (b * w, false)
      rw [dblAut_b, dblAct_b]
      rfl
    · show dblAct (dblAut c) (w, false) = (c * w, false)
      have hc : dblAct (dblAut c) = cDPerm * cDPerm := by
        rw [dblAut_c, map_zpow, dblAct_c, show (2 : ℤ) = 1 + 1 by norm_num,
          zpow_add, zpow_one]
      rw [hc]
      show cDPerm (cDPerm (w, false)) = (c * w, false)
      rfl
  · intro i ih w
    rw [map_inv, map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_eq, ih,
      mul_inv_cancel_left]
  · intro u v hu hv w
    rw [map_mul, map_mul]
    show dblAct (dblAut u) (dblAct (dblAut v) (w, false)) = (u * v * w, false)
    rw [hv, hu, mul_assoc]

theorem dblAut_injective : Function.Injective dblAut := by
  intro x y hxy
  have hx := dblAct_dblAut x 1
  rw [hxy, dblAct_dblAut y 1] at hx
  have h1 : y * 1 = x * 1 := congrArg Prod.fst hx
  rw [mul_one, mul_one] at h1
  exact h1.symm

/-! ## 4.  The operation, and the one closure left -/

/-- The `θ`-image of a single sequence. -/
noncomputable def thetaSeq (g : E) : E :=
  Finsupp.comapDomain (fun i : ℤ => 2 * i) g (fun x _ y _ h => by
    have h' : 2 * x = 2 * y := h
    omega)

@[simp] theorem thetaSeq_apply (g : E) (i : ℤ) : thetaSeq g i = g (2 * i) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem thetaOp_eq_image (B : Set E) : thetaOp B = thetaSeq '' B := by
  refine Set.ext fun f => ?_
  constructor
  · rintro ⟨g, hg, hfg⟩
    refine ⟨g, hg, Finsupp.ext fun i => ?_⟩
    rw [thetaSeq_apply]
    exact (hfg i).symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun i => thetaSeq_apply g i⟩

/-- A sequence with its odd coordinates set to zero. -/
noncomputable def evenSeq (g : E) : E := dblSeq (thetaSeq g)

@[simp] theorem evenSeq_two_mul (g : E) (i : ℤ) : evenSeq g (2 * i) = g (2 * i) := by
  unfold evenSeq
  rw [dblSeq_two_mul, thetaSeq_apply]

theorem evenSeq_odd (g : E) (i : ℤ) (h : ∀ k : ℤ, i ≠ 2 * k) : evenSeq g i = 0 :=
  dblSeq_of_notMem_range _ _ h

/-- **`κ`: set the odd coordinates to zero.**  This is the one operation `θ`
still needs, and it belongs with `ζ` and `π` rather than with the doubling. -/
noncomputable def evenOp (B : Set E) : Set E := evenSeq '' B

theorem evenOp_eq_image (B : Set E) : evenOp B = dblSeq '' (thetaOp B) := by
  unfold evenOp evenSeq
  rw [thetaOp_eq_image, Set.image_image]

/-- The sequences vanishing at every odd coordinate: one fixed set, with no
`B` in it. -/
def oddZero : Set E := {f | ∀ i : ℤ, (∀ k : ℤ, i ≠ 2 * k) → f i = 0}

/-- **`κ` is an agreement condition intersected with one fixed set.**  A
sequence lies in `κ B` exactly when it agrees with some member of `B` on the
even coordinates and vanishes on the odd ones.

This is what makes `κ` cheap rather than a seventh obligation: the first
factor is the operation `ζ` and `π` are both instances of --- agreement with a
member of `B` on a set of coordinates --- and the second is a single set that
does not move with `B`, so `benignTF_ASub_inter` joins them. -/
theorem evenOp_eq_inter (B : Set E) :
    evenOp B
      = {f | ∃ g ∈ B, ∀ i : ℤ, (∃ k : ℤ, i = 2 * k) → f i = g i} ∩ oddZero := by
  refine Set.ext fun f => ?_
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, hg, ?_⟩, fun i hi => evenSeq_odd g i hi⟩
    rintro i ⟨k, rfl⟩
    exact evenSeq_two_mul g k
  · rintro ⟨⟨g, hg, hev⟩, hodd⟩
    refine ⟨g, hg, Finsupp.ext fun i => ?_⟩
    by_cases h : ∃ k : ℤ, i = 2 * k
    · obtain ⟨k, rfl⟩ := h
      rw [evenSeq_two_mul]
      exact (hev (2 * k) ⟨k, rfl⟩).symm
    · push Not at h
      rw [evenSeq_odd g i h]
      exact (hodd i h).symm

theorem ASub_dblSeq_image (C : Set E) : ASub (dblSeq '' C) = (ASub C).map dblAut := by
  unfold ASub
  rw [MonoidHom.map_closure]
  congr 1
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨aElt g, ⟨g, hg, rfl⟩, (aElt_dblSeq g).symm⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨dblSeq g, ⟨g, hg, rfl⟩, aElt_dblSeq g⟩

/-- **The subgroup of the even-coordinate copy is the image of the subgroup of
the `θ`-image.** -/
theorem ASub_evenOp (B : Set E) :
    ASub (evenOp B) = (ASub (thetaOp B)).map dblAut := by
  rw [evenOp_eq_image, ASub_dblSeq_image]

/-- **The subgroup of a `θ`-image is a preimage.** -/
theorem ASub_thetaOp (B : Set E) :
    ASub (thetaOp B) = (ASub (evenOp B)).comap dblAut := by
  rw [ASub_evenOp, Subgroup.comap_map_eq_self_of_injective dblAut_injective]

/-- **Higman's operation `θ`, modulo killing the odd coordinates.**  Everything
the doubling does to the sort and to the coding is discharged here. -/
theorem benignTF_ASub_thetaOp {B : Set E} (h : BenignTF (ASub (evenOp B))) :
    BenignTF (ASub (thetaOp B)) := by
  rw [ASub_thetaOp]
  exact BenignTF.comap f3Overgroup dblAut h

/-- **Higman's operation `θ`, from closure under `κ`** --- in the shape the
field `OperationClosures.theta` asks for. -/
theorem benignTF_ASub_thetaOp_of_evenOp
    (hkappa : ∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (evenOp B)))
    (B : Set E) (h : BenignTF (ASub B)) : BenignTF (ASub (thetaOp B)) :=
  benignTF_ASub_thetaOp (hkappa B h)

/-! ## 5.  `κ`, split into inputs shared with the other operations

`evenOp_eq_inter` writes `κ B` as an agreement condition on the even
coordinates intersected with the fixed set `oddZero`, and
`benignTF_ASub_inter` splits the two.  The agreement half is the operation
`ζ` and `π` are instances of.  The fixed half is the `B`-free statement
below, and it is the `ζ`/`π` lane's "all coded sequences are benign" moved
onto the even coordinates by the doubling --- so it costs that statement plus
`TorsionFreeImageClosure` at `G = N = F₃`, and nothing new. -/

theorem oddZero_eq_image : oddZero = dblSeq '' (Set.univ : Set E) := by
  refine Set.ext fun f => ?_
  constructor
  · intro hf
    refine ⟨thetaSeq f, Set.mem_univ _, Finsupp.ext fun i => ?_⟩
    by_cases h : ∃ k : ℤ, i = 2 * k
    · obtain ⟨k, rfl⟩ := h
      rw [dblSeq_two_mul, thetaSeq_apply]
    · push Not at h
      rw [dblSeq_of_notMem_range _ _ h]
      exact (hf i h).symm
  · rintro ⟨g, _, rfl⟩ i hi
    exact dblSeq_of_notMem_range g i hi

/-- **The sequences vanishing on the odd coordinates carry a benign subgroup**,
given that all coded sequences do. -/
theorem benignTF_ASub_oddZero (himg : TorsionFreeImageClosure)
    (hall : BenignTF (ASub (Set.univ : Set E))) : BenignTF (ASub oddZero) := by
  letI : Group.FG F₃ := ProductFinitePresentation.fg_of_isFinitelyPresented F₃
  rw [oddZero_eq_image, ASub_dblSeq_image]
  exact himg F₃ F₃ IsPowerTorsionFree.of_isMulTorsionFree _ dblAut dblAut_injective hall

/-- **Higman's operation `θ`, from three inputs, none of which is about the
doubling, the sort or the coding.**

The first two are shared with `ρ` and `τ` and with the `ζ`/`π` lane; the third
is the agreement operation those two lanes are both instances of, taken at the
even coordinates. -/
theorem benignTF_ASub_thetaOp_of_inputs (himg : TorsionFreeImageClosure)
    (hall : BenignTF (ASub (Set.univ : Set E)))
    (hagree : ∀ B : Set E, BenignTF (ASub B) →
      BenignTF (ASub {f | ∃ g ∈ B, ∀ i : ℤ, (∃ k : ℤ, i = 2 * k) → f i = g i}))
    (B : Set E) (h : BenignTF (ASub B)) : BenignTF (ASub (thetaOp B)) := by
  refine benignTF_ASub_thetaOp ?_
  rw [evenOp_eq_inter, ASub_inter]
  exact BenignTF.inf (hagree B h) (benignTF_ASub_oddZero himg hall)

/-! ## 6.  `θ` needs nothing of its own

Both halves of `κ` are supplied by the `ζ`/`π`/`ω` lane as it stands, so `θ`
costs no input that is not already priced there --- in particular it does *not*
need `TorsionFreeImageClosure`, which `benignTF_ASub_oddZero` above was paying
for the fixed half.  `Higman.Omega.benignTF_ASub_evenSupport` gets that half
from `OmegaInput` instead, by reading the sequences with even support as `ω₂`
of `ζ Z`; and the agreement half is `Higman.Agree.benignTF_ASub_agreeOp_ker`
at the even coordinates. -/

/-- The even coordinates, in the decidable form `agreeOp` needs. -/
def evenIdx (i : ℤ) : Prop := i % 2 = 0

instance : DecidablePred evenIdx := fun i => inferInstanceAs (Decidable (i % 2 = 0))

theorem evenIdx_iff (i : ℤ) : evenIdx i ↔ ∃ k : ℤ, i = 2 * k := by
  unfold evenIdx
  constructor
  · intro h
    exact ⟨i / 2, by omega⟩
  · rintro ⟨k, rfl⟩
    omega

theorem evenOp_eq_agree_inter (B : Set E) :
    evenOp B = Agree.agreeOp evenIdx B ∩ oddZero := by
  rw [evenOp_eq_inter]
  congr 1
  refine Set.ext fun f => ?_
  constructor
  · rintro ⟨g, hg, hagree⟩
    exact ⟨g, hg, fun i hi => hagree i ((evenIdx_iff i).mp hi)⟩
  · rintro ⟨g, hg, hagree⟩
    exact ⟨g, hg, fun i hi => hagree i ((evenIdx_iff i).mpr hi)⟩

/-- **Higman's operation `θ`, from the `ζ`/`π`/`ω` lane's inputs and nothing
else.**  `hV` is the agreement lane's row input at the even coordinates and `k`
is its `ω` residue; `TorsionFreeImageClosure` does not appear. -/
theorem benignTF_ASub_thetaOp_of_lanes
    (hV : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn evenIdx))))
    (k : Omega.OmegaInput) (B : Set E) (h : BenignTF (ASub B)) :
    BenignTF (ASub (thetaOp B)) := by
  refine benignTF_ASub_thetaOp ?_
  rw [evenOp_eq_agree_inter, ASub_inter]
  refine BenignTF.inf ?_ ?_
  · exact Agree.benignTF_ASub_agreeOp_ker evenIdx hV (Omega.benignTF_ASub_univ k) h
  · exact Omega.benignTF_ASub_evenSupport k

end Seq
end Higman
end GroupApproximation
