import GroupApproximation.GGT.SystolicDiscMirrorFoldQuad
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Reading the distinct mirror fold in the original map

The final map `MirrorQuad.M3` of the three moves embeds in the original map along face rotation.
A dart is read through the three deletions, except that the dart `d1` of the digon is sent back to
`alpha e2` and the dart `d2` of the folded pair to `alpha e1`: in the final map `d1` runs along the
old edge of `e2` and `d2` along the old edge of `e1`.

* `MirrorQuad.tau_facePerm`: the reading `tau` commutes with face rotation.
* `MirrorQuad.tau_injective`: `tau` is injective.
* `MirrorQuad.tau_cases`, `MirrorQuad.vc_alpha`: `tau` agrees with the plain reading `vc` except
  at `d1` and `d2`, and `vc` commutes with reversal.
* `MirrorQuad.exists_tau_eq_of_ne`, `MirrorQuad.tau_d1'''`, `MirrorQuad.tau_d2'''`: every dart
  off the two triangles, and `alpha e1` and `alpha e2`, is read.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open scoped Classical

noncomputable section

universe u

namespace MirrorQuad

variable {M : CombMap.{u}} (Q : MirrorQuad M)

theorem value1_facePerm (x : Q.M1.Dart) :
    EdgeDeletion.value M Q.d (Q.M1.facePerm x) =
      EdgeDeletion.next M Q.d (EdgeDeletion.value M Q.d x) :=
  EdgeDeletion.value_facePerm_eq_next M Q.d x

theorem value3_alpha (x : Q.M3.Dart) :
    EdgeDeletion.value Q.M2 Q.e2'' (Q.M3.alpha x) = Q.M2.alpha (EdgeDeletion.value Q.M2 Q.e2'' x) :=
  EdgeDeletion.value_alpha x

theorem d1'_ne_alpha_e1' : Q.d1' ≠ Q.M1.alpha Q.e1' := Q.ne1_alpha Q.d1_ne_ae1

theorem d2'_ne_alpha_e1' : Q.d2' ≠ Q.M1.alpha Q.e1' := Q.ne1_alpha Q.d2_ne_ae1

theorem e2'_ne_alpha_e1' : Q.e2' ≠ Q.M1.alpha Q.e1' := Q.ne1_alpha Q.e2_ne_ae1

/-- In the final map, `d1` runs along the old edge of `e2`. -/
def rho3 (x : Q.M3.Dart) : Q.M2.Dart :=
  EdgeDeletion.digonBack (M := Q.M2) (a := Q.e2'') Q.d1'' x

/-- After the fold, `d2` runs along the old edge of `e1`. -/
def rho2 (y : Q.M2.Dart) : Q.M1.Dart :=
  EdgeDeletion.digonBack (M := Q.J) (a := Q.e1') Q.d2' y

/-- **The final map read in the original map.** -/
def tau (x : Q.M3.Dart) : M.Dart :=
  EdgeDeletion.value M Q.d (Q.rho2 (Q.rho3 x))

/-- The final map read through the three deletions. -/
def vc (x : Q.M3.Dart) : M.Dart :=
  EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' (EdgeDeletion.value Q.M2 Q.e2'' x))

theorem rho3_of_ne {x : Q.M3.Dart} (h : EdgeDeletion.value Q.M2 Q.e2'' x ≠ Q.d1'') :
    Q.rho3 x = EdgeDeletion.value Q.M2 Q.e2'' x :=
  EdgeDeletion.digonBack_of_ne h

theorem rho3_of_eq {x : Q.M3.Dart} (h : EdgeDeletion.value Q.M2 Q.e2'' x = Q.d1'') :
    Q.rho3 x = Q.M2.alpha Q.e2'' :=
  EdgeDeletion.digonBack_of_eq h

theorem rho2_of_ne {y : Q.M2.Dart} (h : EdgeDeletion.value Q.J Q.e1' y ≠ Q.d2') :
    Q.rho2 y = EdgeDeletion.value Q.J Q.e1' y :=
  EdgeDeletion.digonBack_of_ne h

theorem rho2_of_eq {y : Q.M2.Dart} (h : EdgeDeletion.value Q.J Q.e1' y = Q.d2') :
    Q.rho2 y = Q.M1.alpha Q.e1' :=
  EdgeDeletion.digonBack_of_eq h

theorem rho3_facePerm (x : Q.M3.Dart) : Q.rho3 (Q.M3.facePerm x) = Q.M2.facePerm (Q.rho3 x) :=
  EdgeDeletion.digonBack_facePerm Q.f2_e2'' Q.f2_d1'' Q.e2''_ne_d1'' x

theorem rho2_facePerm (y : Q.M2.Dart) : Q.rho2 (Q.M2.facePerm y) = Q.J.facePerm (Q.rho2 y) :=
  EdgeDeletion.digonBack_facePerm (FoldMap.joined_facePerm_next Q.isFoldable)
    (FoldMap.joined_facePerm_self Q.isFoldable) Q.isFoldable.ne_next.symm y

theorem rho3_ne_d1'' (x : Q.M3.Dart) : Q.rho3 x ≠ Q.d1'' :=
  EdgeDeletion.digonBack_ne (M := Q.M2) (a := Q.e2'') Q.alpha_e2''_ne_d1'' x

theorem rho3_ne_e2'' (x : Q.M3.Dart) : Q.rho3 x ≠ Q.e2'' :=
  EdgeDeletion.digonBack_ne_self (M := Q.M2) (a := Q.e2'') Q.d1'' x

theorem rho2_ne_d2' (y : Q.M2.Dart) : Q.rho2 y ≠ Q.d2' :=
  EdgeDeletion.digonBack_ne (M := Q.J) (a := Q.e1')
    (show Q.J.alpha Q.e1' ≠ Q.d2' from fun e => Q.d2'_ne_alpha_e1' e.symm) y

theorem rho2_ne_e1' (y : Q.M2.Dart) : Q.rho2 y ≠ Q.e1' :=
  EdgeDeletion.digonBack_ne_self (M := Q.J) (a := Q.e1') Q.d2' y

theorem rho2_rho3_ne_d1' (x : Q.M3.Dart) : Q.rho2 (Q.rho3 x) ≠ Q.d1' := by
  by_cases h : EdgeDeletion.value Q.J Q.e1' (Q.rho3 x) = Q.d2'
  · rw [Q.rho2_of_eq h]
    exact Q.d1'_ne_alpha_e1'.symm
  · rw [Q.rho2_of_ne h]
    intro e
    exact Q.rho3_ne_d1'' x (EdgeDeletion.value_injective Q.J Q.e1'
      (show EdgeDeletion.value Q.J Q.e1' (Q.rho3 x) = EdgeDeletion.value Q.J Q.e1' Q.d1'' from e))

theorem rho2_rho3_ne_e2' (x : Q.M3.Dart) : Q.rho2 (Q.rho3 x) ≠ Q.e2' := by
  by_cases h : EdgeDeletion.value Q.J Q.e1' (Q.rho3 x) = Q.d2'
  · rw [Q.rho2_of_eq h]
    exact Q.e2'_ne_alpha_e1'.symm
  · rw [Q.rho2_of_ne h]
    intro e
    exact Q.rho3_ne_e2'' x (EdgeDeletion.value_injective Q.J Q.e1'
      (show EdgeDeletion.value Q.J Q.e1' (Q.rho3 x) = EdgeDeletion.value Q.J Q.e1' Q.e2'' from e))

/-- **The reading commutes with face rotation.** -/
theorem tau_facePerm (x : Q.M3.Dart) : Q.tau (Q.M3.facePerm x) = M.facePerm (Q.tau x) := by
  have hz1 : Q.rho2 (Q.rho3 x) ≠ Q.d1' := Q.rho2_rho3_ne_d1' x
  have hz2 : Q.rho2 (Q.rho3 x) ≠ Q.e1' := Q.rho2_ne_e1' _
  have hz3 : Q.rho2 (Q.rho3 x) ≠ Q.d2' := Q.rho2_ne_d2' _
  have hz4 : Q.rho2 (Q.rho3 x) ≠ Q.e2' := Q.rho2_rho3_ne_e2' x
  have hJ : Q.J.facePerm (Q.rho2 (Q.rho3 x)) = Q.M1.facePerm (Q.rho2 (Q.rho3 x)) := by
    rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne hz1 hz2]
  have h1 : M.facePerm (EdgeDeletion.value M Q.d (Q.rho2 (Q.rho3 x))) ≠ Q.d := by
    intro e
    have h : EdgeDeletion.value M Q.d (Q.rho2 (Q.rho3 x)) = EdgeDeletion.value M Q.d Q.d2' :=
      M.facePerm.injective (e.trans Q.f_d2.symm)
    exact hz3 (EdgeDeletion.value_injective M Q.d h)
  have h2 : M.facePerm (EdgeDeletion.value M Q.d (Q.rho2 (Q.rho3 x))) ≠ M.alpha Q.d := by
    intro e
    have h : EdgeDeletion.value M Q.d (Q.rho2 (Q.rho3 x)) = EdgeDeletion.value M Q.d Q.e2' :=
      M.facePerm.injective (e.trans Q.f_e2.symm)
    exact hz4 (EdgeDeletion.value_injective M Q.d h)
  unfold tau
  rw [Q.rho3_facePerm, Q.rho2_facePerm, hJ, Q.value1_facePerm,
    EdgeDeletion.next_of_ne_of_ne M Q.d h1 h2]

/-- **The reading is injective.** -/
theorem tau_injective : Function.Injective Q.tau := by
  intro x y h
  have h2 : Q.rho2 (Q.rho3 x) = Q.rho2 (Q.rho3 y) := EdgeDeletion.value_injective M Q.d h
  have h3 : Q.rho3 x = Q.rho3 y :=
    EdgeDeletion.digonBack_injective (M := Q.J) (a := Q.e1') Q.d2' h2
  exact EdgeDeletion.digonBack_injective (M := Q.M2) (a := Q.e2'') Q.d1'' h3

/-- The plain reading commutes with reversal. -/
theorem vc_alpha (x : Q.M3.Dart) : Q.vc (Q.M3.alpha x) = M.alpha (Q.vc x) := by
  unfold vc
  rw [Q.value3_alpha, Q.vv_alpha]

theorem value_alpha_e2''_ne_d2' : EdgeDeletion.value Q.J Q.e1' (Q.M2.alpha Q.e2'') ≠ Q.d2' := by
  intro e
  have h1 := congrArg (EdgeDeletion.value M Q.d) e
  rw [Q.vv_alpha] at h1
  exact Q.d2_ne_ae2 h1.symm

theorem tau_eq_vc {x : Q.M3.Dart} (h3 : EdgeDeletion.value Q.M2 Q.e2'' x ≠ Q.d1'')
    (h2 : EdgeDeletion.value Q.J Q.e1' (EdgeDeletion.value Q.M2 Q.e2'' x) ≠ Q.d2') :
    Q.tau x = Q.vc x := by
  unfold tau vc
  rw [Q.rho3_of_ne h3, Q.rho2_of_ne h2]

/-- **The reading differs from the plain reading only at `d1` and `d2`.** -/
theorem tau_cases (x : Q.M3.Dart) :
    Q.tau x = Q.vc x ∨ (Q.vc x = Q.d1 ∧ Q.tau x = M.alpha Q.e2) ∨
      (Q.vc x = Q.d2 ∧ Q.tau x = M.alpha Q.e1) := by
  by_cases h3 : EdgeDeletion.value Q.M2 Q.e2'' x = Q.d1''
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · exact congrArg (fun y : Q.M2.Dart =>
        EdgeDeletion.value M Q.d (EdgeDeletion.value Q.J Q.e1' y)) h3
    · unfold tau
      rw [Q.rho3_of_eq h3, Q.rho2_of_ne Q.value_alpha_e2''_ne_d2']
      exact Q.vv_alpha Q.e2''
  · by_cases h2 : EdgeDeletion.value Q.J Q.e1' (EdgeDeletion.value Q.M2 Q.e2'' x) = Q.d2'
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · exact congrArg (EdgeDeletion.value M Q.d) h2
      · unfold tau
        rw [Q.rho3_of_ne h3, Q.rho2_of_eq h2]
        exact Q.value1_alpha Q.e1'
    · exact Or.inl (Q.tau_eq_vc h3 h2)

/-- The digon dart `d1` is read as `alpha e2`. -/
theorem tau_d1''' : Q.tau Q.d1''' = M.alpha Q.e2 := by
  have h3 : Q.rho3 Q.d1''' = Q.M2.alpha Q.e2'' := Q.rho3_of_eq rfl
  unfold tau
  rw [h3, Q.rho2_of_ne Q.value_alpha_e2''_ne_d2']
  exact Q.vv_alpha Q.e2''

/-- The folded dart `d2` is read as `alpha e1`. -/
theorem tau_d2''' : Q.tau Q.d2''' = M.alpha Q.e1 := by
  have h3 : Q.rho3 Q.d2''' = Q.d2'' := Q.rho3_of_ne (show Q.d2'' ≠ Q.d1'' from Q.ne2 Q.d2_ne_d1)
  have h2 : Q.rho2 Q.d2'' = Q.M1.alpha Q.e1' := Q.rho2_of_eq rfl
  unfold tau
  rw [h3, h2]
  exact Q.value1_alpha Q.e1'

/-- **Every dart off the two triangles and their reversed far sides is read.** -/
theorem exists_tau_eq_of_ne {z : M.Dart} (hd : z ≠ Q.d) (had : z ≠ M.alpha Q.d)
    (hd1 : z ≠ Q.d1) (hd2 : z ≠ Q.d2) (he1 : z ≠ Q.e1) (hae1 : z ≠ M.alpha Q.e1)
    (he2 : z ≠ Q.e2) (hae2 : z ≠ M.alpha Q.e2) : ∃ x, Q.tau x = z := by
  let z1 : Q.M1.Dart := EdgeDeletion.ofValue M Q.d z hd had
  have h11 : z1 ≠ Q.e1' := Q.ne1 he1
  have h12 : z1 ≠ Q.M1.alpha Q.e1' := Q.ne1_alpha hae1
  let z2 : Q.M2.Dart := EdgeDeletion.ofValue Q.J Q.e1' z1 h11 (fun e => h12 e)
  have h21 : z2 ≠ Q.e2'' := Q.ne2 he2
  have h22 : z2 ≠ Q.M2.alpha Q.e2'' := by
    intro e
    have h1 := congrArg (EdgeDeletion.value M Q.d) (congrArg (EdgeDeletion.value Q.J Q.e1') e)
    rw [Q.vv_alpha] at h1
    exact hae2 h1
  let x : Q.M3.Dart := EdgeDeletion.ofValue Q.M2 Q.e2'' z2 h21 h22
  have h3 : EdgeDeletion.value Q.M2 Q.e2'' x ≠ Q.d1'' := Q.ne2 hd1
  have h2 : EdgeDeletion.value Q.J Q.e1' (EdgeDeletion.value Q.M2 Q.e2'' x) ≠ Q.d2' := Q.ne1 hd2
  exact ⟨x, Q.tau_eq_vc h3 h2⟩

end MirrorQuad

end

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.tau_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.tau_injective
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.vc_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.tau_cases
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.tau_d1'''
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.tau_d2'''
#audit_axioms GroupApproximation.GGT.VanKampen.MirrorQuad.exists_tau_eq_of_ne
