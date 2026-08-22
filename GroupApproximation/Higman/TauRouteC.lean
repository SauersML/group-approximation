import GroupApproximation.Higman.ClosuresAssembly
import GroupApproximation.Higman.GeneratedValue

/-!
# Route C: the `τ`-free chain

`Higman.SwapCarrierWitness` proves that every construction mechanism this
repository has for a coded family is excluded for `τ`.  Route C takes the other
exit, and this file is its landing.

`OperationClosures.tau` is consumed in exactly one place ---
`Higman.benignTF_of_higmanGenerated`, on the `tau` constructor --- so `τ` is
spent exactly when a `HigmanGenerated` derivation uses that constructor.  A
repository-wide grep found four such uses.  Three were in
`Higman.GeneratedValue` and have been rewritten in place, on `σ` and the
down-shift `ρ σ ρ`, with every statement unchanged; the fourth was the base
case of a transposition calculus in `HigmanVariableCalculus`, since deleted
outright, so the constructor now has no use anywhere in the repository.

This file supplies the two things that turns into.

## 1.  The `τ`-free fragment, and the record it needs

`Seq.HigmanGeneratedTF` is `Seq.HigmanGenerated` **without the `tau`
constructor**, `OperationClosuresTF` is `OperationClosures` **without the `tau`
field**, and `benignTF_of_higmanGeneratedTF` is the induction joining them.
`operationClosures_of_inputs_tauFree` builds the record from **five** leaves
rather than six: `ρ` is proved (`operationClosures_rho`), and `τ` is gone.

`HigmanGeneratedTF.toHigmanGenerated` is the forgetful map, so nothing is lost:
a `τ`-free derivation is a derivation.

## 2.  What is still owed, and by whom

The chain closes on the `τ`-free record exactly when Higman's Section 2 is
proved in the `τ`-free form,

    HigmanTheoremThreeTF : ∀ B, REset B → Seq.HigmanGeneratedTF B ,

which is the strengthening of `HigmanTheoremThree` that
`reBenignTF_of_inputs_tauFree` consumes.  That is a requirement on the trace
lane, not a theorem this file can prove: it says every relation of the trace
machine must be *built in the variable order it is consumed in*, so that no
coordinate permutation is ever needed.  `Higman.HigmanAtoms` already builds its
relational layer that way --- `freeAt c`, `succRel d`, `diffSet`, `eqRel a b`
are each constructed at an arbitrary index by `σ`-conjugation from an index-`0`
case, so the index is a parameter rather than something to permute afterwards.

## 3.  How far `τ` is derivable, for the record

Section 3 below records the sharp answer to the other half of route C.  On a set
whose two window coordinates are pinned, `τ` is a composite of `ι`,
coordinate-freeing and the pins, with no `τ` anywhere
(`Seq.tauOp_windowClass`).  The general `τ` is the union of these over
`(c, c') ∈ ℤ × ℤ`, and the operation list has only the *binary* union, so the
derivation does not close.  That gap --- uniformity in the window values --- is
the whole of what is unresolved; `notes/W6_TAU_ROUTE_C_2026-08-22.md` explains
why the obvious repair routes back through the transposition calculus.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The `τ`-free fragment -/

/-- **`Seq.HigmanGenerated` without the transposition.**  Every constructor of
the original except `tau`. -/
inductive HigmanGeneratedTF : Set E → Prop
  | zero : HigmanGeneratedTF Zset
  | succ : HigmanGeneratedTF Sset
  | inter {B B' : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF B' →
      HigmanGeneratedTF (B ∩ B')
  | union {B B' : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF B' →
      HigmanGeneratedTF (B ∪ B')
  | rho {B : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF (rhoOp B)
  | sigma {B : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF (sigmaOp B)
  | theta {B : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF (thetaOp B)
  | zeta {B : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF (zetaOp B)
  | pi {B : Set E} : HigmanGeneratedTF B → HigmanGeneratedTF (piOp B)
  | omega {B : Set E} (m : ℕ) (hm : 0 < m) :
      HigmanGeneratedTF B → HigmanGeneratedTF (omegaOp m B)

/-- **A `τ`-free derivation is a derivation.**  Nothing is lost by working in
the fragment. -/
theorem HigmanGeneratedTF.toHigmanGenerated {B : Set E}
    (h : HigmanGeneratedTF B) : HigmanGenerated B := by
  induction h with
  | zero => exact HigmanGenerated.zero
  | succ => exact HigmanGenerated.succ
  | inter _ _ ih ih' => exact HigmanGenerated.inter ih ih'
  | union _ _ ih ih' => exact HigmanGenerated.union ih ih'
  | rho _ ih => exact HigmanGenerated.rho ih
  | sigma _ ih => exact HigmanGenerated.sigma ih
  | theta _ ih => exact HigmanGenerated.theta ih
  | zeta _ ih => exact HigmanGenerated.zeta ih
  | pi _ ih => exact HigmanGenerated.pi ih
  | omega m hm _ ih => exact HigmanGenerated.omega m hm ih

/-! ## 3.  How far `τ` is derivable

Placed here rather than in the fragment above because it is a fact about
Higman's operation list, not about our chain. -/

/-- A set with both window coordinates freed.  This is
`HigmanAtoms.freeAt 1 ∘ HigmanAtoms.freeAt 0`, and
`HigmanAtoms.higmanGenerated_freeAt` generates it; it is spelled out here so
that this file needs no import of that module. -/
def freeWindow (B : Set E) : Set E :=
  {f | ∃ g ∈ B, ∀ i : ℤ, i ≠ 0 → i ≠ 1 → f i = g i}

/-- **`τ` is derivable on a window class.**

If both window coordinates of `B` are pinned, transposing them is the same as
freeing them and re-pinning them the other way round --- an intersection of a
coordinate-freeing with two pins, and no transposition anywhere.  It works
because on `B ∩ pinZero c ∩ pinOne c'` the window of the witness is determined,
so re-pinning cannot pick up a different witness.

The general `τ` is the union of these over all `(c, c') ∈ ℤ × ℤ`, and the
operation list has only the binary union.  That is exactly where derivability
stops. -/
theorem tauOp_windowClass (B : Set E) (c c' : ℤ) :
    tauOp (B ∩ pinZero c ∩ pinOne c')
      = freeWindow (B ∩ pinZero c ∩ pinOne c') ∩ pinZero c' ∩ pinOne c := by
  ext f
  constructor
  · rintro ⟨g, hg, h0, h1, hrest⟩
    have hg0 : g 0 = c := hg.1.2
    have hg1 : g 1 = c' := hg.2
    refine ⟨⟨⟨g, hg, hrest⟩, ?_⟩, ?_⟩
    · show f 0 = c'
      rw [h0, hg1]
    · show f 1 = c
      rw [h1, hg0]
  · rintro ⟨⟨⟨g, hg, hrest⟩, hf0⟩, hf1⟩
    have hg0 : g 0 = c := hg.1.2
    have hg1 : g 1 = c' := hg.2
    have hf0' : f 0 = c' := hf0
    have hf1' : f 1 = c := hf1
    exact ⟨g, hg, by rw [hf0', hg1], by rw [hf1', hg0], hrest⟩

end Seq

/-! ## 2.  The `τ`-free record, and the induction -/

/-- **`OperationClosures` without the `tau` field.**

`ρ` is not a field either: it is proved, by `operationClosures_rho`.  What is
left is the base case `S` and four closures, and
`benignTF_of_higmanGeneratedTF` is the proof that they suffice for every
`τ`-free derivation. -/
structure OperationClosuresTF where
  /-- Higman's base case `S`. -/
  base : BenignTF (Seq.ASub Seq.Sset)
  /-- Closure under `θ`. -/
  theta : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.thetaOp B))
  /-- Closure under `ζ`. -/
  zeta : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.zetaOp B))
  /-- Closure under `π`. -/
  pi : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.piOp B))
  /-- Closure under `ωₘ`, for positive `m`. -/
  omega : ∀ (m : ℕ), 0 < m → ∀ (B : Set Seq.E), BenignTF (Seq.ASub B) →
    BenignTF (Seq.ASub (Seq.omegaOp m B))

/-- **The induction, without `τ`.**  Every `τ`-free derivation gives a benign
subgroup with a torsion-free witness, from five leaves rather than seven. -/
theorem benignTF_of_higmanGeneratedTF (h : OperationClosuresTF) {B : Set Seq.E}
    (hB : Seq.HigmanGeneratedTF B) : BenignTF (Seq.ASub B) := by
  induction hB with
  | zero => exact Seq.benignTF_ASub_Zset
  | succ => exact h.base
  | inter _ _ ih ih' => exact benignTF_ASub_inter ih ih'
  | union _ _ ih ih' => exact benignTF_ASub_union ih ih'
  | rho _ ih => exact operationClosures_rho _ ih
  | sigma _ ih => exact benignTF_ASub_sigmaOp ih
  | theta _ ih => exact h.theta _ ih
  | zeta _ ih => exact h.zeta _ ih
  | pi _ ih => exact h.pi _ ih
  | omega m hm _ ih => exact h.omega m hm _ ih

/-- **The `τ`-free record from five inputs.**

The `τ`-free analogue of `Higman.operationClosures_of_inputs`, which takes six.
`k` is the `ω` residue, `hbase` is Higman's base case `S`, and the three rows
are the ones `Higman.OmegaClosure` and `Higman.OperationClosureTheta` consume.
`ρ` is discharged inside, and `τ` does not appear. -/
theorem operationClosures_of_inputs_tauFree (k : Omega.OmegaInput)
    (hbase : BenignTF (Seq.ASub Seq.Sset))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx)))) :
    OperationClosuresTF :=
  have hzpo := Omega.zeta_pi_omega_closures hhalf hzetaRow k
  { base := hbase
    theta := Seq.benignTF_ASub_thetaOp_of_lanes hevenRow k
    zeta := hzpo.1
    pi := hzpo.2.1
    omega := hzpo.2.2 }

/-- **Higman's Section 2 in the `τ`-free form.**

This is the requirement route C puts on the trace lane, and the only thing
standing between `OperationClosuresTF` and the chain: every recursively
enumerable set must be reachable by a derivation that never permutes
coordinates.

**Nothing inhabits this.** -/
def HigmanTheoremThreeTF : Prop :=
  ∀ B : Set Seq.E, REset B → Seq.HigmanGeneratedTF B

/-- **Higman's Theorem 4, with `τ` off the critical path.**  Every recursively
enumerable set has a benign subgroup with a torsion-free witness, from the
`τ`-free record and the `τ`-free Section 2. -/
theorem benignTF_ASub_of_re_tauFree (h₁ : OperationClosuresTF)
    (h₂ : HigmanTheoremThreeTF) (B : Set Seq.E) (hB : REset B) :
    BenignTF (Seq.ASub B) :=
  benignTF_of_higmanGeneratedTF h₁ (h₂ B hB)

end Higman
end GroupApproximation
