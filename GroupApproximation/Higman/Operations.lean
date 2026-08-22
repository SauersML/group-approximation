import GroupApproximation.Higman.BaseCases
import GroupApproximation.Higman.ShiftOperation

/-!
# The nine Higman operations, and what closure under them gives

Higman's Section 2 says a subset of the sequence space is recursively
enumerable exactly when it is built from two explicit sets, `Z = {0}` and
`S = {(a, a+1) : a ∈ ℤ}`, by nine operations.  His Section 4 says the family of
subsets whose subgroup `A_B` is benign contains those two and is closed under
all nine.  Together they give his Theorem 4, which is the whole of
`Higman.REBenignTF` apart from the transport of Section 5.

This file:

* defines the nine operations on `Set E`;
* defines `HigmanGenerated`, the inductive family built from `Z` and `S` by
  them;
* records which closures are **proved** here --- `ι`, `υ` (`Seq.ASub_inter`,
  `Seq.ASub_union`) and `σ` (`Seq.ASub_sigmaOp`, by an automorphism of `F₃`)
  --- and states the remaining six as one structure, `OperationClosures`;
* proves the induction: the base cases plus the closures give benignness for
  every `HigmanGenerated` set.

So what `REBenignTF` still owes is exactly: the remaining operation closures,
the base case `S`, Higman's Section 2, and the transport of his Section 5.
Each is a separate, classical, independently attackable statement, and
`benignTF_of_higmanGenerated` below is the proof that nothing else is needed to
combine them.

The count of remaining closures has since dropped from six to five: `ρ` is
proved, by `Higman.FlipGroup` over `Higman.TorsionFreeImageClosure`, and
`Higman.ClosuresAssembly` fills the field.  This file is left stated at
Higman's own list, so `OperationClosures` below still carries `rho`; the
smaller input list is `ClosuresAssembly.operationClosures_of_inputs`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  The operations -/

/-- `ρ`: reverse the index. -/
def rhoOp (B : Set E) : Set E := {f | ∃ g ∈ B, ∀ i : ℤ, f i = g (-i)}

/-- `τ`: swap the coordinates `0` and `1`. -/
def tauOp (B : Set E) : Set E :=
  {f | ∃ g ∈ B, f 0 = g 1 ∧ f 1 = g 0 ∧ ∀ i : ℤ, i ≠ 0 → i ≠ 1 → f i = g i}

/-- `θ`: keep the even coordinates. -/
def thetaOp (B : Set E) : Set E := {f | ∃ g ∈ B, ∀ i : ℤ, f i = g (2 * i)}

/-- `ζ`: free the coordinate `0`. -/
def zetaOp (B : Set E) : Set E := {f | ∃ g ∈ B, ∀ i : ℤ, i ≠ 0 → f i = g i}

/-- `π`: free the strictly positive coordinates. -/
def piOp (B : Set E) : Set E := {f | ∃ g ∈ B, ∀ i : ℤ, i ≤ 0 → f i = g i}

/-- The `m`-block of a sequence starting at `m * i`, read as a sequence
supported on `[0, m)`. -/
noncomputable def blockAt (m : ℕ) (i : ℤ) (f : E) : E :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) (m : ℤ))
    (fun j => if j ∈ Finset.Ico (0 : ℤ) (m : ℤ) then f (m * i + j) else 0)
    (by
      intro j hj
      by_contra hcon
      rw [if_neg hcon] at hj
      exact hj rfl)

/-- `ωₘ`: every `m`-block is in the set. -/
noncomputable def omegaOp (m : ℕ) (B : Set E) : Set E :=
  {f | ∀ i : ℤ, blockAt m i f ∈ B}

/-! ## 2.  Higman's set `S` -/

/-- The sequence `(a, a+1)`. -/
noncomputable def succSeq (a : ℤ) : E :=
  Finsupp.single (0 : ℤ) a + Finsupp.single (1 : ℤ) (a + 1)

/-- Higman's set `S`. -/
noncomputable def Sset : Set E := Set.range succSeq

/-! ## 3.  The sets Higman builds -/

/-- The subsets of the sequence space built from `Z` and `S` by the nine
operations.  Higman's Section 2 is the statement that these are exactly the
recursively enumerable ones. -/
inductive HigmanGenerated : Set E → Prop
  | zero : HigmanGenerated Zset
  | succ : HigmanGenerated Sset
  | inter {B B' : Set E} : HigmanGenerated B → HigmanGenerated B' →
      HigmanGenerated (B ∩ B')
  | union {B B' : Set E} : HigmanGenerated B → HigmanGenerated B' →
      HigmanGenerated (B ∪ B')
  | rho {B : Set E} : HigmanGenerated B → HigmanGenerated (rhoOp B)
  | sigma {B : Set E} : HigmanGenerated B → HigmanGenerated (sigmaOp B)
  | tau {B : Set E} : HigmanGenerated B → HigmanGenerated (tauOp B)
  | theta {B : Set E} : HigmanGenerated B → HigmanGenerated (thetaOp B)
  | zeta {B : Set E} : HigmanGenerated B → HigmanGenerated (zetaOp B)
  | pi {B : Set E} : HigmanGenerated B → HigmanGenerated (piOp B)
  | omega {B : Set E} (m : ℕ) (hm : 0 < m) :
      HigmanGenerated B → HigmanGenerated (omegaOp m B)

end Seq

/-! ## 4.  What is still owed at the level of operations -/

/-- **Input: the operation closures Higman's Section 4 still owes, and the base
case `S`.**

Three of the nine closures are proved right here: `ι` and `υ` are lattice
identities (`Seq.ASub_inter`, `Seq.ASub_union` with `BenignTF.inf`,
`BenignTF.sup`), and `σ` is an automorphism of `F₃` (`Seq.ASub_sigmaOp`).  Each
field below is one of Higman's remaining constructions, and each is an HNN
extension or a join of the kind this repository already builds --- which is why
the torsion clause is not a separate obligation.

**The field count is not the cost.**  Since this structure was written, `ρ` has
been proved: `Higman.FlipGroup` reduces it to `Seq.TorsionFreeImageClosure` and
`Higman.TorsionFreeImageClosure` proves that, so
`Higman.ClosuresAssembly.operationClosures_rho` fills the `rho` field outright.
The same file's `operationClosures_of_inputs` builds the whole structure from
what is genuinely still open, which is six things and not seven: the base case
`S`, the `τ` closure, `Omega.OmegaInput`, and three benign rows.  Read that
constructor, not this field list, for the current boundary.

**Nothing inhabits this structure**, and nothing will until those six are
supplied. -/
structure OperationClosures where
  /-- Higman's base case `S`. -/
  base : BenignTF (Seq.ASub Seq.Sset)
  /-- Closure under `ρ`.  **Proved**, in
  `Higman.ClosuresAssembly.operationClosures_rho`; it stays a field only so
  that this structure keeps Higman's own list intact. -/
  rho : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.rhoOp B))
  /-- Closure under `τ`. -/
  tau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.tauOp B))
  /-- Closure under `θ`. -/
  theta : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.thetaOp B))
  /-- Closure under `ζ`. -/
  zeta : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.zetaOp B))
  /-- Closure under `π`. -/
  pi : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) → BenignTF (Seq.ASub (Seq.piOp B))
  /-- Closure under `ωₘ`, for positive `m`.  Higman's Theorem 3 quantifies `ωₘ`
  over the *positive* integers, and the restriction is not cosmetic: `blockAt 0`
  is identically zero, so `ω₀ B` is the whole sequence space whenever `0 ∈ B`,
  and an unrestricted field would silently demand that `A_E` be benign — which
  neither Higman's Lemma 4.10 nor Mikaelian's replacement covers. -/
  omega : ∀ (m : ℕ), 0 < m → ∀ (B : Set Seq.E), BenignTF (Seq.ASub B) →
    BenignTF (Seq.ASub (Seq.omegaOp m B))

/-- The three closures this repository proves, in the torsion-free form. -/
theorem benignTF_ASub_inter {B B' : Set Seq.E} (h : BenignTF (Seq.ASub B))
    (h' : BenignTF (Seq.ASub B')) : BenignTF (Seq.ASub (B ∩ B')) := by
  rw [Seq.ASub_inter]
  exact BenignTF.inf h h'

theorem benignTF_ASub_union {B B' : Set Seq.E} (h : BenignTF (Seq.ASub B))
    (h' : BenignTF (Seq.ASub B')) : BenignTF (Seq.ASub (B ∪ B')) := by
  letI : Group.FG Conj.F₃ :=
    ProductFinitePresentation.fg_of_isFinitelyPresented Conj.F₃
  rw [Seq.ASub_union]
  exact BenignTF.sup h h'

theorem benignTF_ASub_sigmaOp {B : Set Seq.E} (h : BenignTF (Seq.ASub B)) :
    BenignTF (Seq.ASub (Seq.sigmaOp B)) := by
  have hmap : Seq.ASub (Seq.sigmaOp B)
      = (Seq.ASub B).comap (Seq.shiftEquiv.symm).toMonoidHom := by
    rw [Seq.ASub_sigmaOp, ← Seq.shiftEquiv_toMonoidHom]
    exact Subgroup.map_equiv_eq_comap_symm' Seq.shiftEquiv (Seq.ASub B)
  rw [hmap]
  exact BenignTF.congr Seq.shiftEquiv.symm h

/-- **The induction.**  With the base cases and the closures, every set Higman
builds has a benign subgroup, with a torsion-free witness. -/
theorem benignTF_of_higmanGenerated (h : OperationClosures) {B : Set Seq.E}
    (hB : Seq.HigmanGenerated B) : BenignTF (Seq.ASub B) := by
  induction hB with
  | zero => exact Seq.benignTF_ASub_Zset
  | succ => exact h.base
  | inter _ _ ih ih' => exact benignTF_ASub_inter ih ih'
  | union _ _ ih ih' => exact benignTF_ASub_union ih ih'
  | rho _ ih => exact h.rho _ ih
  | sigma _ ih => exact benignTF_ASub_sigmaOp ih
  | tau _ ih => exact h.tau _ ih
  | theta _ ih => exact h.theta _ ih
  | zeta _ ih => exact h.zeta _ ih
  | pi _ ih => exact h.pi _ ih
  | omega m hm _ ih => exact h.omega m hm _ ih

end Higman
end GroupApproximation
