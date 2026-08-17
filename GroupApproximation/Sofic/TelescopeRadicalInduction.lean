import GroupApproximation.Sofic.CoronaRadicalPullback

/-!
# Climbing a tower of quotients inside the MF radical

Section 37 of the multi-mover dossier computes the MF radical of a wreath
product over an ascending HNN coset space by pushing labels along the telescope

```text
W₀ ↠ W₁ ↠ W₂ ↠ ⋯ ↠ P,
```

each stage identifying the lamps in one fibre.  Each single stage is supplied
by a collapse theorem — the first by the compression defect, the later ones by
torsion collapse in the abelianised lamp.  What chains them is the radical
pullback, and that induction is what this file provides.

## The statement

Suppose each stage kernel lies in the radical *of the group that stage starts
from*:

```text
ker ψₙ ≤ Res_MF Wₙ .
```

That is exactly what a collapse theorem gives, and it is a statement about `Wₙ`,
not about `W₀`.  The induction converts it into a statement about `W₀`: the
composite kernel `ker Φₙ` lies in `Res_MF W₀` for every `n`.

The step is the pullback: once `ker Φₙ ≤ Res_MF W₀`, the radical of `W₀` is the
preimage of the radical of `Wₙ`, so an element killed one stage later has its
`Φₙ`-image in `ker ψₙ ≤ Res_MF Wₙ`, hence lies in the preimage.

## The limit

A tower is only useful if the limit kernel is the union of the finite ones.
That is not automatic and is proved separately for the telescope — a finitely
supported configuration meets finitely many fibres, so one stage already sees
the whole partition of its support.  Here it is an explicit hypothesis of the
limit lemma, discharged by the caller.

Nothing in this file knows what a lamp is; it is pure radical bookkeeping, and
applies to any tower whose stages collapse.
-/

namespace GroupApproximation
namespace TelescopeRadicalInduction

universe u

variable {W : Type u} [Group W]

/-! ## One step -/

/-- The pullback step.  If a normal subgroup already lies in the radical, an
element whose image lies in the radical of the quotient lies in the radical. -/
theorem mem_of_map_mem {N : Subgroup W} [N.Normal]
    (hN : N ≤ coronaMFResidual W) {x : W}
    (hx : QuotientGroup.mk' N x ∈ coronaMFResidual (W ⧸ N)) :
    x ∈ coronaMFResidual W := by
  rw [coronaMFResidual_eq_comap N hN]
  exact Subgroup.mem_comap.mpr hx

/-- Transport of invisibility across the first isomorphism theorem, forwards:
an element invisible after passing to the quotient by `ker φ` is invisible after
applying a surjection `φ` with that kernel. -/
theorem mem_coronaMFResidual_map {G H : Type u} [Group G] [Group H]
    (phi : G →* H) (hphi : Function.Surjective phi) {x : G}
    (hx : QuotientGroup.mk' phi.ker x ∈ coronaMFResidual (G ⧸ phi.ker)) :
    phi x ∈ coronaMFResidual H := by
  intro X hX rho
  have hval : QuotientGroup.quotientKerEquivOfSurjective phi hphi
      (QuotientGroup.mk' phi.ker x) = phi x := QuotientGroup.kerLift_mk phi x
  have h := hx X hX
    (rho.comp (QuotientGroup.quotientKerEquivOfSurjective phi hphi).toMonoidHom)
  rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hval] at h

/-- Transport of invisibility across the first isomorphism theorem, backwards. -/
theorem mem_coronaMFResidual_quotient {G H : Type u} [Group G] [Group H]
    (phi : G →* H) (hphi : Function.Surjective phi) {x : G}
    (hx : phi x ∈ coronaMFResidual H) :
    QuotientGroup.mk' phi.ker x ∈ coronaMFResidual (G ⧸ phi.ker) := by
  intro X hX rho
  have hval : QuotientGroup.quotientKerEquivOfSurjective phi hphi
      (QuotientGroup.mk' phi.ker x) = phi x := QuotientGroup.kerLift_mk phi x
  have h := hx X hX
    (rho.comp (QuotientGroup.quotientKerEquivOfSurjective phi hphi).symm.toMonoidHom)
  rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hval,
    MulEquiv.symm_apply_apply] at h

/-! ## The tower -/

variable {V : ℕ → Type u} [∀ n, Group (V n)]

/-- A tower of quotients of `W`: stage maps out of `W`, and connecting maps
between consecutive stages that compose correctly. -/
structure Tower (W : Type u) [Group W] (V : ℕ → Type u) [∀ n, Group (V n)] where
  /-- The map from the source to stage `n`. -/
  stage : ∀ n, W →* V n
  /-- The connecting map from stage `n` to stage `n+1`. -/
  step : ∀ n, V n →* V (n + 1)
  /-- The tower commutes. -/
  comp : ∀ n, (step n).comp (stage n) = stage (n + 1)

variable (T : Tower W V)

theorem stage_succ_apply (n : ℕ) (x : W) :
    T.stage (n + 1) x = T.step n (T.stage n x) := by
  rw [← T.comp n, MonoidHom.comp_apply]

/-- **The induction.**  If the first stage kernel lies in the radical of the
source, and every later step kernel lies in the radical of the stage it starts
from, then every composite stage kernel lies in the radical of the source. -/
theorem ker_stage_le_coronaMFResidual
    (hbase : (T.stage 0).ker ≤ coronaMFResidual W)
    (hstep : ∀ n, (T.step n).ker ≤ coronaMFResidual (V n))
    (_hnormal : ∀ n, ((T.stage n).ker).Normal)
    (hpull : ∀ n, ∀ x : W, T.stage n x ∈ coronaMFResidual (V n) →
      x ∈ coronaMFResidual W) :
    ∀ n, (T.stage n).ker ≤ coronaMFResidual W := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n _ =>
      intro x hx
      rw [MonoidHom.mem_ker, stage_succ_apply] at hx
      exact hpull n x (hstep n (MonoidHom.mem_ker.mpr hx))

/-- The hypothesis `hpull` above is exactly what the pullback supplies once the
stage kernel is known to be radical; this packages the two together so a caller
supplies only the collapse theorems. -/
theorem pull_of_ker_le {n : ℕ} [((T.stage n).ker).Normal]
    (hn : (T.stage n).ker ≤ coronaMFResidual W)
    (hsurj : Function.Surjective (T.stage n)) (x : W)
    (hx : T.stage n x ∈ coronaMFResidual (V n)) :
    x ∈ coronaMFResidual W := by
  -- transport along the isomorphism `W ⧸ ker (stage n) ≃* V n`
  exact mem_of_map_mem hn (mem_coronaMFResidual_quotient (T.stage n) hsurj hx)

/-! ## The limit -/

/-- **The limit kernel.**  If the kernel of the limit map is the union of the
stage kernels, it lies in the radical.  The union hypothesis is the telescope's
finite-support fact and is discharged by the caller. -/
theorem ker_limit_le_coronaMFResidual {P : Type u} [Group P] (limit : W →* P)
    (hstages : ∀ n, (T.stage n).ker ≤ coronaMFResidual W)
    (hunion : ∀ x ∈ limit.ker, ∃ n, x ∈ (T.stage n).ker) :
    limit.ker ≤ coronaMFResidual W := by
  intro x hx
  obtain ⟨n, hn⟩ := hunion x hx
  exact hstages n hn

/-- **The radical is the limit kernel exactly, when the limit is MF.**  With the
limit kernel inside the radical, the pullback computes the radical, and an MF
limit makes the correction term vanish. -/
theorem coronaMFResidual_eq_ker_limit {P : Type u} [Group P]
    (limit : W →* P)
    (hker : limit.ker ≤ coronaMFResidual W)
    (hsurj : Function.Surjective limit)
    (hMF : coronaMFResidual P = ⊥) :
    coronaMFResidual W = limit.ker := by
  refine le_antisymm ?_ hker
  intro x hx
  rw [coronaMFResidual_eq_comap limit.ker hker, Subgroup.mem_comap] at hx
  have himg : limit x ∈ coronaMFResidual P :=
    mem_coronaMFResidual_map limit hsurj hx
  rw [hMF, Subgroup.mem_bot] at himg
  exact MonoidHom.mem_ker.mpr himg

end TelescopeRadicalInduction
end GroupApproximation
