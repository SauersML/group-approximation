import GroupApproximation.BooneHigman.Metabelian.VdKInjCocycleFibre
import GroupApproximation.BooneHigman.Metabelian.VdKInjActTruth
import GroupApproximation.Meta.AxiomGuard

/-!
# Row cocycles and retractions, part 2: based cocycles are exactly retractions

Lane `bh-met-91y`.  Write `H = rowStab(e_last) ≤ St_{n+1}(R)` and `P = vdkRowParSubgroup n R`,
the parabolic image, with `P ≤ H`.  Everything here holds unconditionally, for every
commutative `R` and every `n`.

* `vdkInjCocycle_RetractAt n R`: some `φ : H →* St_n(R)` has `φ (stab g) = g`.
* `vdkInjCocycle_cocycle_iff_retract`: **a based row cocycle exists iff `RetractAt n R`**.
  - `⟹` (`vdkInjCocycle_retract_of_cocycle`): `φ h = (psi h)⁻¹`, read off the fibre over
    `e_last` (`VdKInjCocycleFibre.lean`).
  - `⟸` (`vdkInjCocycle_cocycle_of_retract`): `Φ(u, g) = φ(sec u · g · sec(u M_g)⁻¹)` on the
    orbit of `e_last`, and `1` off it.  Unlike `VdKInjActTruth.lean`, this does **not** use Step A
    (`vdkInjCoset_RowStabAt`).  The twist already lies in `H` (`vdkInjAct_twist_mem`), and `φ`
    is defined on all of `H`.
* `vdkInjCocycle_ParRetractAt n R`: the same retraction, on `P` only.  It is equivalent to
  injectivity of `K2Stab n R` (`vdkInjCocycle_parRetract_iff_injective`).
* `RetractAt ⟹ ParRetractAt` by restriction.  The converse holds under Step A (`H ≤ P`).

**LOUD (strength).**  A based cocycle is thus the same thing as a retraction of `stab` defined
on the whole stabiliser `H`.  Proving that needs either Step A plus injectivity, or a direct
construction of `φ` on `H`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colVec_zero)

variable {n : ℕ} {R : Type*} [CommRing R]

variable (n R) in
/-- A retraction of `stab : St_n(R) → St_{n+1}(R)` defined on the whole stabiliser
`rowStab(e_last)`. -/
def vdkInjCocycle_RetractAt : Prop :=
  ∃ φ : vdkInjCoset_rowStab n R →* St n R,
    ∀ g : St n R, φ ⟨stab n R g, vdkInjCoset_stab_mem g⟩ = g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_RetractAt

/-- **Cocycle ⟹ retraction**: `h ↦ (psi h)⁻¹`. -/
theorem vdkInjCocycle_retract_of_cocycle {c : vdkInjAct_Cocycle n R}
    (hc : vdkInjAct_IsCocycle c) (hb : vdkInjAct_IsBased c) : vdkInjCocycle_RetractAt n R := by
  refine ⟨MonoidHom.mk' (fun h ↦ (vdkInjCocycle_psi hc h.1)⁻¹) ?_, ?_⟩
  · intro a b
    show (vdkInjCocycle_psi hc (a.1 * b.1))⁻¹ =
      (vdkInjCocycle_psi hc a.1)⁻¹ * (vdkInjCocycle_psi hc b.1)⁻¹
    rw [vdkInjCocycle_psi_mul hc a.2 b.2, mul_inv_rev]
  · intro g
    show (vdkInjCocycle_psi hc (stab n R g))⁻¹ = g
    rw [vdkInjCocycle_psi_stab hc hb, inv_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_retract_of_cocycle

open Classical in
/-- A map `H →* St_n(R)`, extended by `1` off `H`. -/
noncomputable def vdkInjCocycle_ext (φ : vdkInjCoset_rowStab n R →* St n R)
    (g : St (n + 1) R) : St n R :=
  if hg : g ∈ vdkInjCoset_rowStab n R then φ ⟨g, hg⟩ else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_ext

theorem vdkInjCocycle_ext_of_mem (φ : vdkInjCoset_rowStab n R →* St n R) {g : St (n + 1) R}
    (hg : g ∈ vdkInjCoset_rowStab n R) : vdkInjCocycle_ext φ g = φ ⟨g, hg⟩ := by
  rw [vdkInjCocycle_ext, dif_pos hg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_ext_of_mem

theorem vdkInjCocycle_ext_mul (φ : vdkInjCoset_rowStab n R →* St n R) {a b : St (n + 1) R}
    (ha : a ∈ vdkInjCoset_rowStab n R) (hb : b ∈ vdkInjCoset_rowStab n R) :
    vdkInjCocycle_ext φ (a * b) = vdkInjCocycle_ext φ a * vdkInjCocycle_ext φ b := by
  rw [vdkInjCocycle_ext_of_mem φ (mul_mem ha hb), vdkInjCocycle_ext_of_mem φ ha,
    vdkInjCocycle_ext_of_mem φ hb]
  exact map_mul φ ⟨a, ha⟩ ⟨b, hb⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_ext_mul

open Classical in
/-- The multiplicative function of a retraction: `φ(sec u · g · sec(u M_g)⁻¹)` on the orbit of
`e_last`, and `1` off it. -/
noncomputable def vdkInjCocycle_phi (φ : vdkInjCoset_rowStab n R →* St n R)
    (u : Fin (n + 1) → R) (g : St (n + 1) R) : St n R :=
  if vdkInjAct_Orb u then
    vdkInjCocycle_ext φ (vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹)
  else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_phi

theorem vdkInjCocycle_phi_pos (φ : vdkInjCoset_rowStab n R →* St n R) {u : Fin (n + 1) → R}
    (hu : vdkInjAct_Orb u) (g : St (n + 1) R) :
    vdkInjCocycle_phi φ u g =
      vdkInjCocycle_ext φ (vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹) := by
  rw [vdkInjCocycle_phi, if_pos hu]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_phi_pos

theorem vdkInjCocycle_phi_neg (φ : vdkInjCoset_rowStab n R →* St n R) {u : Fin (n + 1) → R}
    (hu : ¬vdkInjAct_Orb u) (g : St (n + 1) R) : vdkInjCocycle_phi φ u g = 1 := by
  rw [vdkInjCocycle_phi, if_neg hu]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_phi_neg

/-- `vdkInjCocycle_phi φ` is multiplicative along the row action.  No Step A is needed: the
twist lies in `rowStab(e_last)` by `vdkInjAct_twist_mem`. -/
theorem vdkInjCocycle_phi_mul (φ : vdkInjCoset_rowStab n R →* St n R) (u : Fin (n + 1) → R)
    (g g' : St (n + 1) R) :
    vdkInjCocycle_phi φ u g * vdkInjCocycle_phi φ (vdkInjAct_row u g) g' =
      vdkInjCocycle_phi φ u (g * g') := by
  by_cases hu : vdkInjAct_Orb u
  · have hu' := vdkInjAct_Orb_row hu g
    have hq : vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹ *
        (vdkInjAct_sec (vdkInjAct_row u g) * g' *
          (vdkInjAct_sec (vdkInjAct_row (vdkInjAct_row u g) g'))⁻¹) =
        vdkInjAct_sec u * (g * g') * (vdkInjAct_sec (vdkInjAct_row u (g * g')))⁻¹ := by
      rw [vdkInjAct_row_mul]
      group
    rw [vdkInjCocycle_phi_pos φ hu g, vdkInjCocycle_phi_pos φ hu' g',
      vdkInjCocycle_phi_pos φ hu (g * g'),
      ← vdkInjCocycle_ext_mul φ (vdkInjAct_twist_mem hu g) (vdkInjAct_twist_mem hu' g'), hq]
  · have hu' : ¬vdkInjAct_Orb (vdkInjAct_row u g) := fun h ↦ hu (vdkInjAct_Orb_of_row h)
    rw [vdkInjCocycle_phi_neg φ hu g, vdkInjCocycle_phi_neg φ hu' g',
      vdkInjCocycle_phi_neg φ hu (g * g'), one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_phi_mul

/-- The cocycle of a retraction is based: at `e_last`, a stabilized root is `stab x_{ij}(a)`,
and `φ` sends it to `x_{ij}(a)`. -/
theorem vdkInjCocycle_phi_based (φ : vdkInjCoset_rowStab n R →* St n R)
    (hφ : ∀ g : St n R, φ ⟨stab n R g, vdkInjCoset_stab_mem g⟩ = g) :
    vdkInjAct_IsBased (fun u i j hij a ↦ vdkInjCocycle_phi φ u (x i j hij a)) := by
  intro i j hij h' a
  show vdkInjCocycle_phi φ (Pi.single (Fin.last n) 1) (x i.castSucc j.castSucc h' a) =
    x i j hij a
  have he : vdkInjAct_Orb (Pi.single (Fin.last n) (1 : R)) := ⟨1, vdkInjAct_row_one _⟩
  have hrow : vdkInjAct_row (Pi.single (Fin.last n) (1 : R)) (x i.castSucc j.castSucc h' a) =
      Pi.single (Fin.last n) 1 :=
    (vdkInjCoset_mem_rowStab _).mp (vdkInjCoset_x_mem _ _ h' a (Fin.castSucc_ne_last i))
  rw [vdkInjCocycle_phi_pos φ he, hrow, vdkInjAct_sec_base, one_mul, inv_one, mul_one,
    ← stab_x i j hij a, vdkInjCocycle_ext_of_mem φ (vdkInjCoset_stab_mem _), hφ]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_phi_based

/-- **Retraction ⟹ cocycle**, with no Step A. -/
theorem vdkInjCocycle_cocycle_of_retract (h : vdkInjCocycle_RetractAt n R) :
    ∃ c : vdkInjAct_Cocycle n R, vdkInjAct_IsCocycle c ∧ vdkInjAct_IsBased c := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨fun u i j hij a ↦ vdkInjCocycle_phi φ u (x i j hij a),
    vdkInjAct_isCocycle_of_mul (vdkInjCocycle_phi φ) (vdkInjCocycle_phi_mul φ),
    vdkInjCocycle_phi_based φ hφ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_cocycle_of_retract

/-- **Unconditional equivalence**: based row cocycles are exactly retractions on `H`. -/
theorem vdkInjCocycle_cocycle_iff_retract :
    (∃ c : vdkInjAct_Cocycle n R, vdkInjAct_IsCocycle c ∧ vdkInjAct_IsBased c) ↔
      vdkInjCocycle_RetractAt n R :=
  ⟨fun ⟨_, hc, hb⟩ ↦ vdkInjCocycle_retract_of_cocycle hc hb, vdkInjCocycle_cocycle_of_retract⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_cocycle_iff_retract

theorem vdkInjCocycle_injective_of_retract (h : vdkInjCocycle_RetractAt n R) :
    Function.Injective (K2Stab n R) := by
  obtain ⟨c, hc, hb⟩ := vdkInjCocycle_cocycle_of_retract h
  exact vdkInjAct_K2Stab_injective_of_cocycle hc hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_injective_of_retract

theorem vdkInjCocycle_rowPar_zero (g : St n R) :
    vdkRowPar ((0 : Fin n → R), g) = stab n R g := by
  rw [vdkRowPar_apply, colVec_zero, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_rowPar_zero

theorem vdkInjCocycle_stab_mem_par (g : St n R) : stab n R g ∈ vdkRowParSubgroup n R :=
  (mem_vdkRowParSubgroup _).mpr ⟨((0 : Fin n → R), g), vdkInjCocycle_rowPar_zero g⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_stab_mem_par

variable (n R) in
/-- A retraction of `stab` defined only on the parabolic image `P`. -/
def vdkInjCocycle_ParRetractAt : Prop :=
  ∃ φ : vdkRowParSubgroup n R →* St n R,
    ∀ g : St n R, φ ⟨stab n R g, vdkInjCocycle_stab_mem_par g⟩ = g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_ParRetractAt

/-- A retraction on `P` makes `stab` injective. -/
theorem vdkInjCocycle_stab_injective_of_parRetract (h : vdkInjCocycle_ParRetractAt n R) :
    Function.Injective (stab n R) := by
  obtain ⟨φ, hφ⟩ := h
  intro g g' hgg
  have h1 : φ ⟨stab n R g, vdkInjCocycle_stab_mem_par g⟩ =
      φ ⟨stab n R g', vdkInjCocycle_stab_mem_par g'⟩ :=
    congrArg φ (Subtype.ext hgg)
  rwa [hφ, hφ] at h1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_stab_injective_of_parRetract

theorem vdkInjCocycle_injective_of_parRetract (h : vdkInjCocycle_ParRetractAt n R) :
    Function.Injective (K2Stab n R) := by
  intro u v huv
  refine Subtype.ext (vdkInjCocycle_stab_injective_of_parRetract h ?_)
  exact congrArg Subtype.val huv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_injective_of_parRetract

/-- Injectivity of `K2Stab n R` gives the retraction on `P`: the `St_n(R)`-component of the
unique `vdkRowPar` preimage. -/
theorem vdkInjCocycle_parRetract_of_injective (hK : Function.Injective (K2Stab n R)) :
    vdkInjCocycle_ParRetractAt n R := by
  have hinj := vdkRowParInjective_of_K2Stab_injective hK
  refine ⟨MonoidHom.mk' (fun h ↦ (vdkInjAct_pre h.1).2)
    (fun a b ↦ vdkInjAct_pre_mul hinj a.2 b.2), ?_⟩
  intro g
  have h := vdkInjAct_pre_rowPar hinj ((0 : Fin n → R), g)
  rw [vdkInjCocycle_rowPar_zero] at h
  exact congrArg Prod.snd h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_parRetract_of_injective

/-- **Unconditional**: a retraction on `P` is the same as injectivity of `K2Stab n R`. -/
theorem vdkInjCocycle_parRetract_iff_injective :
    vdkInjCocycle_ParRetractAt n R ↔ Function.Injective (K2Stab n R) :=
  ⟨vdkInjCocycle_injective_of_parRetract, vdkInjCocycle_parRetract_of_injective⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_parRetract_iff_injective

/-- Restriction from `H` to `P ≤ H`. -/
theorem vdkInjCocycle_parRetract_of_retract (h : vdkInjCocycle_RetractAt n R) :
    vdkInjCocycle_ParRetractAt n R := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.comp (Subgroup.inclusion (vdkInjCoset_rowPar_le (n := n) (R := R))), fun g ↦ ?_⟩
  exact hφ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_parRetract_of_retract

/-- Under Step A (`H ≤ P`), a retraction on `P` restricts to one on `H`. -/
theorem vdkInjCocycle_retract_of_parRetract (hA : vdkInjCoset_RowStabAt n R)
    (h : vdkInjCocycle_ParRetractAt n R) : vdkInjCocycle_RetractAt n R := by
  have hA' : vdkInjCoset_rowStab n R ≤ vdkRowParSubgroup n R := hA
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.comp (Subgroup.inclusion hA'), fun g ↦ ?_⟩
  exact hφ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_retract_of_parRetract

/-- **Strength (LOUD).**  Under Step A, a based cocycle, a retraction on `H` and injectivity of
`K2Stab n R` are all equivalent. -/
theorem vdkInjCocycle_retract_iff_injective_of_rowStab (hA : vdkInjCoset_RowStabAt n R) :
    vdkInjCocycle_RetractAt n R ↔ Function.Injective (K2Stab n R) :=
  ⟨vdkInjCocycle_injective_of_retract,
    fun hK ↦ vdkInjCocycle_retract_of_parRetract hA (vdkInjCocycle_parRetract_of_injective hK)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_retract_iff_injective_of_rowStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
