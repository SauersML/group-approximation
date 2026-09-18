import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama
import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplit
import GroupApproximation.BooneHigman.V.Transitive
import GroupApproximation.Meta.AxiomGuard

/-!
# Classes of localised elements of `K` in the abelianisation of the envelope

Let `V = envelopeV X H = V_Y(K)` with `Y = Fin 2 × X` and `K = envelopeK 2 H`.

* `gentorsionLoc K p : K →* V_Y(K)`, `k ↦ localize p (cantorHom k)`;
* `gentorsion_class_localize_sq`: if `V_Y ≤ ⁅V, V⁆` and `H` is self-similar, the class of
  `localize p (cantorHom (envelopeEmbed 2 h))` in the abelianisation is a square;
* `gentorsion_class_localize_eq`: localisations of one element at two nonempty words have the
  same class;
* `gentorsion_loc_sq`: the class of `gentorsionLoc K p k` lies in the range of squaring;
* `gentorsion_mem_closure_image`: images of a generating set generate the image;
* `gentorsionGens H S a`: the localisations of `S` at `[]` and at `[a]`.

Route: `gentorsion_cantorHom_decomp`, localised at `p`, gives `s * b0 * b1` with `s ∈ V_Y`,
`b0, b1 ∈ V` (`coneBaseHom_mem`, `gentorsion_half_mem`) and `t * b1 = b0 * t` for the `V_Y`
element `t = localize p (coneMap gentorsionSwap 1)` (`gentorsion_conj_base`); then
`gentorsion_class_sq`.  Conjugacy of localisations: `exists_mapsCone_of_ne_nil` and
`MapsCone.conj_localize`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

/-- `k ↦ localize p (cantorHom k)`, as a homomorphism into `V_Y(K)`. -/
def gentorsionLoc {Y : Type*} [Finite Y] (K : Subgroup (TreeAut Y)) (p : List Y) :
    ↥K →* ↥(roverNekrashevych Y K) :=
  ((localize p).comp (cantorHom.comp K.subtype)).codRestrict (roverNekrashevych Y K)
    fun k => localize_mem_roverNekrashevych K p k.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsionLoc

variable {X : Type*} [Finite X] {H : Subgroup (TreeAut X)}

theorem gentorsion_half_mem (hH : IsSelfSimilar H) {h : TreeAut X} (hh : h ∈ H)
    (y : envelopeY X 2) : gentorsionHalf h y ∈ envelopeV X H := by
  obtain ⟨i, x⟩ := y
  rw [gentorsionHalf_apply]
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact cantorHom_mem_roverNekrashevych _ (Subgroup.mem_map_of_mem (envelopeEmbed 2) (hH h hh x))
  · rw [if_neg hi]
    exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_half_mem

theorem gentorsion_class_localize_sq
    (hVc : higmanThompsonV (envelopeY X 2) ≤ ⁅envelopeV X H, envelopeV X H⁆)
    (hH : IsSelfSimilar H) {h : TreeAut X} (hh : h ∈ H) (p : List (envelopeY X 2))
    (hg : localize p (cantorHom (envelopeEmbed 2 h)) ∈ envelopeV X H) :
    ∃ u : Abelianization ↥(envelopeV X H),
      (Abelianization.of : ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H)) ⟨_, hg⟩ =
        u ^ 2 := by
  have hloc : ∀ (w : List (envelopeY X 2)) (g : Equiv.Perm (Cantor (envelopeY X 2))),
      g ∈ envelopeV X H → localize w g ∈ envelopeV X H := fun w _ hg' => localize_mem_rn _ w hg'
  have hhalf : ∀ y, gentorsionHalf h y ∈ envelopeV X H := gentorsion_half_mem hH hh
  have hs : localize p (coneMap gentorsion_conesSeparated
      (TreeAut.rootPerm (envelopeEmbed 2 h)) 1) ∈ ⁅envelopeV X H, envelopeV X H⁆ :=
    hVc (localize_mem_higmanThompsonV (coneMap_mem_higmanThompsonV gentorsion_conesSeparated
      (N := 1) (fun _ => rfl) _) p)
  obtain ⟨hsV, hs'⟩ := gentorsion_mem_commutator_subtype hs
  have ht : localize p (coneMap gentorsion_conesSeparated gentorsionSwap 1) ∈ envelopeV X H :=
    hloc p _ (higmanThompsonV_le_rn _ (coneMap_mem_higmanThompsonV gentorsion_conesSeparated
      (N := 1) (fun _ => rfl) gentorsionSwap))
  have hb0 := hloc p _ (coneBaseHom_mem hloc gentorsion_conesSeparated hhalf)
  have hb1 := hloc p _ (coneBaseHom_mem hloc gentorsion_conesSeparated
    (G := fun y => gentorsionHalf h (gentorsionSwap y)) fun y => hhalf (gentorsionSwap y))
  refine gentorsion_class_sq hsV hs' ht hb0 hb1 hg ?_ ?_
  · rw [gentorsion_cantorHom_decomp, map_mul, map_mul]
  · have hc := congrArg (localize p)
      (gentorsion_conj_base gentorsion_conesSeparated gentorsionSwap (gentorsionHalf h))
    rw [map_mul, map_mul] at hc
    exact hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_class_localize_sq

theorem gentorsion_class_localize_eq [Nontrivial X] {k : TreeAut (envelopeY X 2)}
    {w v : List (envelopeY X 2)} (hw : w ≠ []) (hv : v ≠ [])
    (hwV : localize w (cantorHom k) ∈ envelopeV X H)
    (hvV : localize v (cantorHom k) ∈ envelopeV X H) :
    (Abelianization.of : ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H)) ⟨_, hwV⟩ =
      (Abelianization.of : ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H)) ⟨_, hvV⟩ := by
  obtain ⟨f, hf, hmaps⟩ := exists_mapsCone_of_ne_nil hw hv
  exact gentorsion_class_eq_of_conj (higmanThompsonV_le_rn _ hf) hwV hvV
    (hmaps.conj_localize (cantorHom k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_class_localize_eq

theorem gentorsion_loc_sq
    (hVc : higmanThompsonV (envelopeY X 2) ≤ ⁅envelopeV X H, envelopeV X H⁆)
    (hH : IsSelfSimilar H) (p : List (envelopeY X 2)) (k : ↥(envelopeK 2 H)) :
    (Abelianization.of : ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H))
        (gentorsionLoc (envelopeK 2 H) p k) ∈
      (powMonoidHom 2 :
        Abelianization ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H)).range := by
  obtain ⟨h, hh, hk⟩ := Subgroup.mem_map.mp k.2
  have hg : localize p (cantorHom (envelopeEmbed 2 h)) ∈ envelopeV X H :=
    localize_mem_roverNekrashevych _ p (Subgroup.mem_map_of_mem (envelopeEmbed 2) hh)
  obtain ⟨u, hu⟩ := gentorsion_class_localize_sq hVc hH hh p hg
  have e : gentorsionLoc (envelopeK 2 H) p k = ⟨localize p (cantorHom (envelopeEmbed 2 h)), hg⟩ :=
    Subtype.ext (show localize p (cantorHom ↑k) = localize p (cantorHom (envelopeEmbed 2 h)) by
      rw [hk])
  refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
  exact ((congrArg (Abelianization.of : ↥(envelopeV X H) →* Abelianization ↥(envelopeV X H))
    e).trans hu).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_loc_sq

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
