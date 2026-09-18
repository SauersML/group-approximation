import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreathEmbedConeV
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragCantor
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplitEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting an embedded tree automorphism at the first letter

For `Y = envelopeY X 2 = Fin 2 × X` and the one-letter cones `c y = [y]`:

* `gentorsion_cantorHom_split`: `cantorHom k = coneMap (rootPerm k) (y ↦ cantorHom (state k [y]))`;
* `gentorsion_conj_base`: `coneMap τ 1 * coneMap 1 (G0 ∘ τ) = coneMap 1 G0 * coneMap τ 1`;
* `gentorsion_states_eq`: the state of `envelopeEmbed 2 h` at `(i, x)` equals
  `gentorsionHalf h (i, x) * gentorsionHalf h (swap i, x)`, where `gentorsionHalf h` is the
  state on the `0`-copy and `1` on the `1`-copy;
* `gentorsion_cantorHom_decomp`: `cantorHom (envelopeEmbed 2 h)` is a `V_Y` cone permutation
  times `coneBaseHom (gentorsionHalf h)` times its conjugate by the copy swap.

Route: `frag_cantorHom_prepend` with `TreeAut.smul_singleton` and `coneMap_prepend`; the
states are split pointwise by `state_envelopeEmbed` and a case split on `Fin 2`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

theorem gentorsion_conesSeparated {Y : Type*} : ConesSeparated (fun y : Y => [y]) :=
  conesSeparated_of_length (N := 1) (fun _ _ h => List.singleton_inj.mp h) fun _ => rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_conesSeparated

theorem gentorsion_cantorHom_split {Y : Type*} (k : TreeAut Y) :
    cantorHom k = coneMap gentorsion_conesSeparated (TreeAut.rootPerm k)
      (fun y => cantorHom (TreeAut.state k [y])) := by
  refine Equiv.ext fun z => ?_
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (length_firstWord 1 z)
  obtain ⟨y, rfl⟩ : ∃ y, z = prepend [a] y := ⟨dropN 1 z, by rw [← ha, prepend_firstWord]⟩
  rw [frag_cantorHom_prepend, TreeAut.smul_singleton]
  exact (coneMap_prepend gentorsion_conesSeparated (TreeAut.rootPerm k)
    (fun y => cantorHom (TreeAut.state k [y])) a y).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_cantorHom_split

theorem gentorsion_conj_base {X ι : Type*} {c : ι → List X} (hsep : ConesSeparated c)
    (τ : Equiv.Perm ι) (G0 : ι → Equiv.Perm (Cantor X)) :
    coneMap hsep τ 1 * coneMap hsep 1 (fun i => G0 (τ i)) =
      coneMap hsep 1 G0 * coneMap hsep τ 1 := by
  refine (coneMap_mul hsep τ 1 1 fun i => G0 (τ i)).trans
    (Eq.trans ?_ (coneMap_mul hsep 1 τ G0 1).symm)
  exact congrArg₂ (coneMap hsep) ((mul_one τ).trans (one_mul τ).symm)
    (funext fun i => (one_mul (G0 (τ i))).trans (mul_one (G0 (τ i))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_conj_base

variable {X : Type*}

/-- The swap of the two copies of `X` in `Fin 2 × X`. -/
def gentorsionSwap : Equiv.Perm (envelopeY X 2) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsionSwap

theorem gentorsionSwap_apply (i : Fin 2) (x : X) :
    gentorsionSwap (i, x) = (Equiv.swap (0 : Fin 2) 1 i, x) := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsionSwap_apply

/-- The state of `envelopeEmbed 2 h` at a letter of the `0`-copy, and `1` on the `1`-copy. -/
def gentorsionHalf (h : TreeAut X) (y : envelopeY X 2) : Equiv.Perm (Cantor (envelopeY X 2)) :=
  if y.1 = 0 then cantorHom (envelopeEmbed 2 (TreeAut.state h [y.2])) else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsionHalf

theorem gentorsionHalf_apply (h : TreeAut X) (i : Fin 2) (x : X) :
    gentorsionHalf h (i, x) =
      if i = 0 then cantorHom (envelopeEmbed 2 (TreeAut.state h [x])) else 1 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsionHalf_apply

theorem gentorsion_states_eq (h : TreeAut X) (y : envelopeY X 2) :
    cantorHom (TreeAut.state (envelopeEmbed 2 h) [y]) =
      gentorsionHalf h y * gentorsionHalf h (gentorsionSwap y) := by
  obtain ⟨i, x⟩ := y
  rw [state_envelopeEmbed, gentorsionSwap_apply, gentorsionHalf_apply, gentorsionHalf_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Equiv.swap_apply_left, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), mul_one]
  · obtain rfl : i = 1 := (by decide : ∀ j : Fin 2, j ≠ 0 → j = 1) i hi
    rw [Equiv.swap_apply_right, if_neg hi, if_pos rfl, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_states_eq

theorem gentorsion_base_split (h : TreeAut X) :
    coneMap gentorsion_conesSeparated 1
        (fun y : envelopeY X 2 => cantorHom (TreeAut.state (envelopeEmbed 2 h) [y])) =
      coneBaseHom gentorsion_conesSeparated (gentorsionHalf h) *
        coneBaseHom gentorsion_conesSeparated (fun y => gentorsionHalf h (gentorsionSwap y)) :=
  (congrArg (coneMap gentorsion_conesSeparated 1) (funext (gentorsion_states_eq h))).trans
    (map_mul (coneBaseHom gentorsion_conesSeparated) (gentorsionHalf h)
      (fun y => gentorsionHalf h (gentorsionSwap y)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_base_split

theorem gentorsion_cantorHom_decomp (h : TreeAut X) :
    cantorHom (envelopeEmbed 2 h) =
      coneMap gentorsion_conesSeparated (TreeAut.rootPerm (envelopeEmbed 2 h)) 1 *
        coneBaseHom gentorsion_conesSeparated (gentorsionHalf h) *
        coneBaseHom gentorsion_conesSeparated (fun y => gentorsionHalf h (gentorsionSwap y)) := by
  rw [mul_assoc, ← gentorsion_base_split, ← coneMap_eq_mul]
  exact gentorsion_cantorHom_split _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gentorsion_cantorHom_decomp

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
