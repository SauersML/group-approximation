import GroupApproximation.Manuscript.MFRecognition.PositiveBranchFiniteQuotients
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronization

/-!
# `lem:positive-branch`: the case `e ∈ INF`

> **Lemma (the case `e ∈ INF`).**  If `e ∈ INF`, then `R̂_e` admits a tracial
> MF realization; in particular, it is MF.
>
> *Proof.*  Let `e ∈ INF`, so that `Q_e = Q_+`, `N_e = N_+`, `q_e = q_+`, and
> `α_e(i(f)) = q_+(f)`, `α_e(v i(f) v⁻¹) = 1`.  By `lem:finite-rope` it
> suffices to show that `R_e` admits a tracial MF realization, and by
> `lem:tensor-sync` applied to `Γ = Γ_e`, `Q = Q_+`, `S = S_e` and `τ = α_e`,
> it suffices to produce the data of that lemma.
>
> The group `K_e` is residually finite by `lem:central-rope`(1), so it admits
> a tracial MF realization by `lem:rf-regular`; and `Γ_e`, the central HNN
> extension of `K_e` over `L_e`, admits one by `cor:central-hnn`.
>
> [the finite quotients: `PositiveBranchFiniteQuotients`]

The group-theoretic paragraph of the printed proof is proved with no open
leaves in `PositiveBranchFiniteQuotients`.  The two analytic steps the printed
proof cites — `cor:central-hnn` and the last clause of `lem:tensor-sync` —
are authored by the `hnn-permanence` and `tensor-sync` lanes.  They are
carried here as the fields of `PositiveBranchInputs`, quoted exactly as
printed, and every theorem below takes that structure as a leading binder; the
conclusions are the printed statements.

`lem:rf-regular` is *not* an input: the repository already proves it, as
`HNNCoronaConjugatorSentenceAudit.residuallyFinite_isRegularlyRealized`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.SecondLevelIndexSets

/-! ## 1.  The two analytic steps the printed proof cites -/

/-- **The two analytic theorems the proof of `lem:positive-branch` cites.**

Both are statements of the manuscript's own Section `sec:prelim`, formalized
by the `hnn-permanence` and `tensor-sync` lanes; the positive branch consumes
them and proves nothing about them. -/
structure PositiveBranchInputs : Type where
  /-- **`cor:central-hnn` (central HNN extensions).**

  > If `G` admits a tracial MF realization and `S ≤ G` is any subgroup, then
  > `⟨G, t | [t,s] = 1 (s ∈ S)⟩` admits a tracial MF realization.

  Printed proof: "Apply `thm:hnn-permanence` with `θ` the inclusion of `S`,
  with `ι` any injective `*`-homomorphism of `A` into a norm matrix corona,
  and with `W = 1`." -/
  centralHNN : ∀ (G : Type) [Group G] [Countable G],
    IsRegularlyRealized G → ∀ S : Subgroup G,
      IsRegularlyRealized (HNNExtension G S S (MulEquiv.refl S))
  /-- **`lem:tensor-sync` (tensor synchronization), final clause.**

  > Let `Γ` be a countable group with a tracial MF realization
  > `(A_1, ρ_1, τ_1)`, let `Q` be a countable group with homomorphisms
  > `β_n : Q → B_n` to finite groups such that every `q ≠ 1` satisfies
  > `β_n(q) ≠ 1` for all large `n`, let `S ≤ Γ`, and let `τ : S → Q` be a
  > homomorphism.  Suppose that for every `n` there is a homomorphism
  > `λ_n : Γ → G_n` to a finite group with `ker(λ_n|_S) ≤ ker(β_n ∘ τ)`.
  > Then ... `⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s)) (s ∈ S)⟩` admits a tracial MF
  > realization, and in particular is MF. -/
  tensorSynchronization : ∀ (Gamma : Type) [Group Gamma] [Countable Gamma]
      (Q : Type) [Group Q] [Countable Q] (B G : ℕ → Type)
      [∀ n, Group (B n)] [∀ n, Finite (B n)] [∀ n, Group (G n)]
      [∀ n, Finite (G n)],
    IsRegularlyRealized Gamma →
      ∀ beta : ∀ n, Q →* B n,
        (∀ q : Q, q ≠ 1 → ∃ N, ∀ n, N ≤ n → beta n q ≠ 1) →
          ∀ (S : Subgroup Gamma) (tau : ↥S →* Q) (lambda : ∀ n, Gamma →* G n),
            (∀ n, ((lambda n).comp S.subtype).ker ≤ ((beta n).comp tau).ker) →
              IsRegularlyRealized (TwistedHNN S tau)

/-! ## 2.  The lemma -/

variable {e : Nat.Partrec.Code}
variable {H C F P Qplus Q K0 Rhat : Type}
variable [Group H] [Group C] [Group F] [Group P] [Group Qplus] [Group Q]
variable [Group K0] [Group Rhat]

/-- "The group `K_e` is residually finite by `lem:central-rope`(1), so it
admits a tracial MF realization by `lem:rf-regular`." -/
theorem isRegularlyRealized_ropeBase
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat) :
    IsRegularlyRealized (RopeBase K0 F P) := by
  letI : Countable (RopeBase K0 F P) := D.countable_K
  letI : Group.ResiduallyFinite (RopeBase K0 F P) := D.residuallyFinite_K
  exact residuallyFinite_isRegularlyRealized (RopeBase K0 F P)

/-- "and `Γ_e`, the central HNN extension of `K_e` over `L_e`, admits one by
`cor:central-hnn`." -/
theorem isRegularlyRealized_centralRope (I : PositiveBranchInputs)
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat) :
    IsRegularlyRealized (CentralRope D.L0 (D.j.comp D.qplus)) := by
  letI : Countable (RopeBase K0 F P) := D.countable_K
  exact I.centralHNN (RopeBase K0 F P) (isRegularlyRealized_ropeBase D)
    (ropeEdge D.L0 (D.j.comp D.qplus))

/-- **`lem:positive-branch`, first clause.**  "If `e ∈ INF`, then `R_e` admits
a tracial MF realization."  This is `lem:tensor-sync` applied to `Γ = Γ_e`,
`Q = Q_+`, `S = S_e` and `τ = α_e`, with the finite quotients of
`PositiveBranchFiniteQuotients`. -/
theorem isRegularlyRealized_twistedRope (I : PositiveBranchInputs)
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat)
    (hINF : InfiniteDomain e) :
    IsRegularlyRealized
      (TwistedHNN (ropeSubgroup D.L0 (D.j.comp D.qplus) D.i0) D.alpha) := by
  classical
  letI : Countable P := D.countable_P
  letI : Group.ResiduallyFinite P := D.residuallyFinite_P
  letI : Countable Q := D.countable_Q
  letI : Countable (CentralRope D.L0 (D.j.comp D.qplus)) := D.countable_Gamma
  -- "choose finite-index normal subgroups `P_1 ≥ P_2 ≥ ⋯` of `P` with trivial
  -- intersection, let `r_n : P → C_n = P/P_n`"
  obtain ⟨T⟩ := exists_descendingFiniteIndexChain P
  -- `π_0 = α_e`, read in `Q_+` through the identification `Q_e = Q_+`
  have hpi0gen : ∀ f : F,
      ((D.equiv_Q_Qplus hINF).toMonoidHom.comp D.alpha)
          (ropeGenS D.L0 (D.j.comp D.qplus) D.i0 f) = D.qplus f := by
    intro f
    show (D.equiv_Q_Qplus hINF)
        (D.alpha (ropeGenS D.L0 (D.j.comp D.qplus) D.i0 f)) = D.qplus f
    rw [D.alpha_gen f]
    exact D.qe_eq_qplus hINF f
  have hpi0conj : ∀ f : F,
      ((D.equiv_Q_Qplus hINF).toMonoidHom.comp D.alpha)
          (ropeGenConjS D.L0 (D.j.comp D.qplus) D.i0 f) = 1 := by
    intro f
    show (D.equiv_Q_Qplus hINF)
        (D.alpha (ropeGenConjS D.L0 (D.j.comp D.qplus) D.i0 f)) = 1
    rw [D.alpha_genConj f, map_one]
  refine I.tensorSynchronization (CentralRope D.L0 (D.j.comp D.qplus)) Q
    (fun n => T.Quot n) (fun n => SwapProduct (T.Quot n))
    (isRegularlyRealized_centralRope I D)
    (fun n => (T.beta D.j n).comp (D.equiv_Q_Qplus hINF).toMonoidHom) ?_
    (ropeSubgroup D.L0 (D.j.comp D.qplus) D.i0) D.alpha
    (fun n => ropeLambda D.L0 (D.j.comp D.qplus) (T.proj n)) ?_
  · -- "every `q ≠ 1` satisfies `β_n(q) ≠ 1` for all large `n`"
    intro q hq
    have hq' : (D.equiv_Q_Qplus hINF) q ≠ 1 :=
      (MulEquiv.map_ne_one_iff (D.equiv_Q_Qplus hINF)).mpr hq
    exact T.beta_ne_one_eventually D.j D.j_injective hq'
  · -- `ker(λ_n|_{S_e}) ≤ ker(β_n ∘ α_e)`
    intro n s hs
    have hle := ker_ropeLambda_restrict_le D.L0 (D.j.comp D.qplus)
      (T.proj n) D.i0 D.qplus (T.beta D.j n)
      ((D.equiv_Q_Qplus hINF).toMonoidHom.comp D.alpha) D.pi1
      (fun _ => rfl) hpi0gen hpi0conj D.pi1_gen D.pi1_genConj
    exact hle hs

/-- **`lem:positive-branch`, exactly as printed.**

"If `e ∈ INF`, then `R̂_e` admits a tracial MF realization; in particular, it
is MF."  The passage from `R_e` to `R̂_e` is `lem:finite-rope`. -/
theorem manuscriptPositiveBranch (I : PositiveBranchInputs)
    (D : RecognitionInputs e H C F P Qplus Q K0 Rhat)
    (hINF : InfiniteDomain e) :
    IsRegularlyRealized Rhat ∧ IsOperatorMF Rhat := by
  letI : Countable Rhat := D.countable_Rhat
  have hR : IsRegularlyRealized Rhat :=
    isRegularlyRealized_of_mulEquiv D.equiv_Rhat.symm
      (isRegularlyRealized_twistedRope I D hINF)
  exact ⟨hR, isOperatorMF_of_isRegularlyRealized hR⟩

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
