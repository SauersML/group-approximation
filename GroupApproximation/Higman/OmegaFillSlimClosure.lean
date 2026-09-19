import GroupApproximation.Higman.OmegaFillTowerTransfer
import GroupApproximation.Higman.OmegaTowerStageThree

/-!
# The `ωₘ` closure, reduced to one benignness statement about the slim tower

`Omega.OmegaTowerInput` asks for a tower with *two* properties: `W_B` benign
and the Britton descent `F₃ ∩ W_B ≤ A_{ωₘ B}`.  The concrete slim tower
`Omega.slimTower` of `Higman.OmegaTowerStageThree` is the group in which the
second one is proved, that being the point of building it over the free group
`⟨b, c⟩` rather than over a benign witness.  Everything below is stated with
that descent as a named hypothesis, `SlimDescent`; it is discharged by
`Omega.slimTower_descent`, and `Higman.OmegaFillSlimClosureClosed` performs
the substitution.  Keeping the two apart costs one definition and keeps this
file --- the part that is pure interface --- independent of the normal-form
chain.

Given the descent, the input collapses to its first field, and it does so in
two shapes.

* `SlimWBenign` asks for `W_B` benign **in the slim tower itself**.  Note that
  this does not ask the slim tower to be finitely presented --- it cannot be,
  its first stage centralizes a subgroup of infinite rank --- only that some
  finitely presented torsion-free group contains it with a finitely generated
  subgroup cutting `W_B` out.
* `SlimLinkedBenignTower` asks instead for a **second** tower, receiving the
  slim one injectively, whose `W_B` is benign.  This is Mikaelian's own shape:
  the second tower is the fat one, built over benign witnesses, and the
  injection is his Lemma 2.4 ---
  `HNNSubextension.injective_of_isSubextensionHom` in this repository, already
  applied to the first stage in `Higman.OmegaFatSlimCanonicalThree`.  It gives
  the same conclusion without proving the first shape, because the descent
  travels forward along the injection (`Omega.TowerHom.descent`) rather than
  the benignness travelling back.

**Nothing inhabits any structure below.**
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-! ## 1.  The descent, as a hypothesis -/

/-- **The Britton half of `Omega.TowerClosure` for the slim tower**, named so
that the reductions below can be stated before it is substituted for. -/
def SlimDescent : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ B : Set E, (0 : E) ∈ B → ∀ x : F₃,
    (slimTower m).emb x ∈ W (slimTower m) B → x ∈ ASub (omegaOp m B)

/-- **`TowerClosure` for the slim tower is one benignness statement.** -/
theorem towerClosure_slimTower (hd : SlimDescent) {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) (hb : BenignTF (W (slimTower m) B)) :
    TowerClosure (slimTower m) B where
  benign := hb
  descent := hd m hm B h0

/-- **`ωₘ` at `B`, from benignness of `W_B` in the slim tower alone.** -/
theorem benignTF_ASub_omegaOp_of_slimBenign (hd : SlimDescent) {m : ℕ}
    (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    (hb : BenignTF (W (slimTower m) B)) :
    BenignTF (ASub (omegaOp m B)) :=
  benignTF_ASub_omegaOp_of_tower hm (slimTower m) h0
    (towerClosure_slimTower hd hm h0 hb)

/-! ## 2.  The residue, in the slim tower -/

/-- **Input: `W_B` is benign in the slim tower.**  This is what remains of
`Omega.OmegaInput` once the slim descent is in hand.

**Nothing inhabits this structure.** -/
structure SlimWBenign : Prop where
  /-- For every positive `m` and every `B` containing the zero sequence whose
  coded subgroup is benign, `W_B` is benign in the slim tower. -/
  benign : ∀ (m : ℕ), 0 < m → ∀ B : Set E, (0 : E) ∈ B → BenignTF (ASub B) →
    BenignTF (W (slimTower m) B)

/-- **The slim benignness statement discharges the tower input.** -/
theorem omegaTowerInput_of_slimWBenign (hd : SlimDescent) (h : SlimWBenign) :
    OmegaTowerInput :=
  ⟨fun m hm B h0 hB =>
    ⟨slimTower m, towerClosure_slimTower hd hm h0 (h.benign m hm B h0 hB)⟩⟩

/-- **... and hence Higman's `ωₘ` closure.** -/
theorem omegaInput_of_slimWBenign (hd : SlimDescent) (h : SlimWBenign) :
    OmegaInput :=
  omegaInput_of (omegaTowerInput_of_slimWBenign hd h)

/-! ## 3.  The residue, in a second tower

The fat tower is finitely presented and torsion-free, so
`Omega.benignTF_W_of_gen` reduces its benignness obligation to benignness of
the second copy of `A_B`; what it does not have is a normal form, and it does
not need one, because the descent arrives from the slim tower along the
injection. -/

/-- **Input: a benign tower receiving the slim tower.**

**Nothing inhabits this structure.** -/
structure SlimLinkedBenignTower : Prop where
  /-- For every positive `m` and every admissible `B`, some tower receives the
  slim tower injectively and has a benign `W_B`. -/
  linked : ∀ (m : ℕ), 0 < m → ∀ B : Set E, (0 : E) ∈ B → BenignTF (ASub B) →
    ∃ (T' : Tower m) (Φ : TowerHom (slimTower m) T'),
      Function.Injective Φ.map ∧ BenignTF (W T' B)

/-- **The linked form discharges the tower input.**  The tower produced is the
*target*: it inherits the descent from the slim tower through
`Omega.TowerHom.descent`, and supplies the benignness itself. -/
theorem omegaTowerInput_of_slimLinked (hd : SlimDescent)
    (h : SlimLinkedBenignTower) : OmegaTowerInput :=
  ⟨fun m hm B h0 hB => by
    obtain ⟨T', Φ, hinj, hb⟩ := h.linked m hm B h0 hB
    exact ⟨T', towerClosure_of_towerHom Φ hinj (hd m hm B h0) hb⟩⟩

/-- **... and hence Higman's `ωₘ` closure.** -/
theorem omegaInput_of_slimLinked (hd : SlimDescent)
    (h : SlimLinkedBenignTower) : OmegaInput :=
  omegaInput_of (omegaTowerInput_of_slimLinked hd h)

/-! ## 4.  What either form buys

`A_E` and `A_{oddZero}` come from the `ω` input alone
(`Omega.benignTF_ASub_univ`, `Omega.benignTF_ASub_evenSupport`), so the two
statements below are the two remaining `Agree` inputs this lane owes the `ζ`,
`π` and `θ` closures. -/

/-- **The subgroup of all coded sequences is benign**, from the slim
residue. -/
theorem benignTF_ASub_univ_of_slimWBenign (hd : SlimDescent) (h : SlimWBenign) :
    BenignTF (ASub (Set.univ : Set E)) :=
  benignTF_ASub_univ (omegaInput_of_slimWBenign hd h)

/-- **The even-support sequences are benign**, from the slim residue. -/
theorem benignTF_ASub_evenSupport_of_slimWBenign (hd : SlimDescent)
    (h : SlimWBenign) :
    BenignTF (ASub {f : E | ∀ i : ℤ, (∀ k : ℤ, i ≠ 2 * k) → f i = 0}) :=
  benignTF_ASub_evenSupport (omegaInput_of_slimWBenign hd h)

end Omega
end Higman
end GroupApproximation
