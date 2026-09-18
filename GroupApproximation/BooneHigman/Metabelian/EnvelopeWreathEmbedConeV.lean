import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreathEmbedCone
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import GroupApproximation.BooneHigman.V.Supports
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# Cone maps inside Higman–Thompson and Röver–Nekrashevych groups

For a separated family of words `c : ι → List X` (`EnvelopeWreathEmbedCone.lean`):

* `coneMap_eq_mul`: `coneMap σ G = coneMap σ 1 * coneMap 1 G`;
* `coneMap_single`: `coneMap 1 (Pi.mulSingle i s) = localize (c i) s`;
* `coneMap_mem_higmanThompsonV`: when all words have one length, `coneMap σ 1 ∈ V_X`;
* `conePermHom : Perm ι →* Perm (Cantor X)` and `coneBaseHom : (ι → Perm) →* Perm`;
* `coneBaseHom_mem`: for finite `ι`, a subgroup closed under localisation contains
  `coneBaseHom G` as soon as it contains every `G i`;
* `localize_mem_commutator`: localisation preserves `⁅V, V⁆` when it preserves `V`;
* `exists_words`: a finite type has an injective family of words of one length over a
  nontrivial alphabet;
* `localize_mem_rn`: `V_X(H)` is closed under localisation.

Route: `coneBaseHom G` is the product of the `coneBaseHom (Pi.mulSingle i (G i))`
(`Subgroup.pi_mem_of_mulSingle_mem` on the comap); the generators of `V_X(H)` are closed under
localisation by `localize_mem_higmanThompsonV` and `localize_append`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} {ι : Type*} {c : ι → List X}

theorem coneMap_eq_mul (hsep : ConesSeparated c) (σ : Equiv.Perm ι)
    (G : ι → Equiv.Perm (Cantor X)) : coneMap hsep σ G = coneMap hsep σ 1 * coneMap hsep 1 G := by
  refine Eq.trans ?_ (coneMap_mul hsep σ 1 1 G).symm
  exact congrArg₂ (coneMap hsep) (mul_one σ).symm (funext fun i => (one_mul (G i)).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_eq_mul

theorem coneMap_single [DecidableEq ι] (hsep : ConesSeparated c) (i : ι)
    (s : Equiv.Perm (Cantor X)) : coneMap hsep 1 (Pi.mulSingle i s) = localize (c i) s := by
  refine Equiv.ext fun x => ?_
  by_cases hx : ∃ j, IsStreamPrefix (c j) x
  · obtain ⟨j, hj⟩ := hx
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hj
    by_cases hij : j = i
    · subst hij
      simp only [coneMap_prepend hsep, Pi.mulSingle_eq_same, localize_apply_prepend,
        Equiv.Perm.one_apply]
    · have hn : ¬ IsStreamPrefix (c i) (prepend (c j) z) := fun h => hij (hsep j i z h).symm
      simp only [coneMap_prepend hsep, Pi.mulSingle_eq_of_ne hij, Equiv.Perm.one_apply,
        localize_apply_of_not hn]
  · exact (coneMap_of_not hsep 1 (Pi.mulSingle i s) hx).trans
      (localize_apply_of_not (fun h => hx ⟨i, h⟩) s).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_single

theorem coneMap_mem_higmanThompsonV [Finite X] (hsep : ConesSeparated c) {N : ℕ}
    (hlen : ∀ i, (c i).length = N) (σ : Equiv.Perm ι) :
    coneMap hsep σ 1 ∈ higmanThompsonV X := by
  refine mem_higmanThompsonV.mpr ⟨N, fun w hw => ?_⟩
  by_cases hc : ∃ i, c i = w
  · obtain ⟨i, rfl⟩ := hc
    exact ⟨c (σ i), fun x => coneMap_prepend hsep σ 1 i x⟩
  · refine ⟨w, fun x => coneMap_of_not hsep σ 1 ?_⟩
    rintro ⟨i, hi⟩
    have e : (c i).length = w.length := (hlen i).trans hw.symm
    exact hc ⟨i, (prefix_of_isStreamPrefix_of_length_le hi (isStreamPrefix_prepend w x)
      e.le).eq_of_length e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_mem_higmanThompsonV

/-- `σ ↦ coneMap σ 1`: permuting the cones by prefix substitution. -/
def conePermHom (hsep : ConesSeparated c) : Equiv.Perm ι →* Equiv.Perm (Cantor X) :=
  MonoidHom.mk' (fun σ => coneMap hsep σ 1) fun σ τ => by
    refine Eq.trans ?_ (coneMap_mul hsep σ τ 1 1).symm
    exact congrArg (coneMap hsep (σ * τ))
      (funext fun _ => (mul_one (1 : Equiv.Perm (Cantor X))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.conePermHom

theorem conePermHom_apply (hsep : ConesSeparated c) (σ : Equiv.Perm ι) :
    conePermHom hsep σ = coneMap hsep σ 1 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.conePermHom_apply

/-- `G ↦ coneMap 1 G`: acting by `G i` inside the cone of `c i`. -/
def coneBaseHom (hsep : ConesSeparated c) :
    (ι → Equiv.Perm (Cantor X)) →* Equiv.Perm (Cantor X) :=
  MonoidHom.mk' (fun G => coneMap hsep 1 G) fun G H => by
    refine Eq.trans ?_ (coneMap_mul hsep 1 1 G H).symm
    exact congrArg₂ (coneMap hsep) (mul_one (1 : Equiv.Perm ι)).symm rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneBaseHom

theorem coneBaseHom_mem [Finite ι] {C : Subgroup (Equiv.Perm (Cantor X))}
    (hloc : ∀ (w : List X) (g : Equiv.Perm (Cantor X)), g ∈ C → localize w g ∈ C)
    (hsep : ConesSeparated c) {G : ι → Equiv.Perm (Cantor X)} (hG : ∀ i, G i ∈ C) :
    coneBaseHom hsep G ∈ C := by
  classical
  refine Subgroup.pi_mem_of_mulSingle_mem (H := C.comap (coneBaseHom hsep)) G fun i => ?_
  show coneMap hsep 1 (Pi.mulSingle i (G i)) ∈ C
  rw [coneMap_single hsep]
  exact hloc (c i) (G i) (hG i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneBaseHom_mem

theorem localize_mem_commutator {V : Subgroup (Equiv.Perm (Cantor X))}
    (hloc : ∀ (w : List X) (g : Equiv.Perm (Cantor X)), g ∈ V → localize w g ∈ V)
    (w : List X) {g : Equiv.Perm (Cantor X)} (hg : g ∈ ⁅V, V⁆) : localize w g ∈ ⁅V, V⁆ := by
  have hmap : V.map (localize w) ≤ V :=
    Subgroup.map_le_iff_le_comap.2 fun h hh => hloc w h hh
  have h1 := Subgroup.mem_map_of_mem (localize w) hg
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hmap hmap h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.localize_mem_commutator

theorem exists_words (κ : Type*) [Finite κ] (Y : Type*) [Nontrivial Y] :
    ∃ (N : ℕ) (w : κ → List Y), Function.Injective w ∧ ∀ i, (w i).length = N := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  obtain ⟨a, b, hab⟩ := exists_pair_ne Y
  refine ⟨n, fun i => List.ofFn fun j : Fin n => if j = e i then b else a,
    fun i i' h => ?_, fun i => List.length_ofFn⟩
  by_contra hne
  have h1 : (if e i = e i then b else a) = if e i = e i' then b else a :=
    congrFun (List.ofFn_injective h) (e i)
  rw [if_pos rfl, if_neg (e.injective.ne hne)] at h1
  exact hab h1.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_words

theorem localize_mem_rn [Finite X] (H : Subgroup (TreeAut X)) (w : List X)
    {g : Equiv.Perm (Cantor X)} (hg : g ∈ roverNekrashevych X H) :
    localize w g ∈ roverNekrashevych X H := by
  have hle : roverNekrashevych X H ≤ (roverNekrashevych X H).comap (localize w) := by
    refine Subgroup.closure_le.mpr ?_
    rintro f (hf | ⟨v, h, hh, rfl⟩)
    · exact higmanThompsonV_le_rn H (localize_mem_higmanThompsonV hf w)
    · have e := localize_mem_roverNekrashevych H (w ++ v) hh
      rw [localize_append] at e
      exact e
  exact hle hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.localize_mem_rn

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
