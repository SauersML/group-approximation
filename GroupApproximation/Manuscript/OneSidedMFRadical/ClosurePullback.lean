import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Sofic.MFCamouflageRadical
import GroupApproximation.Algebra.CountableInstances

/-!
# The MF closure pulls back along a universally factoring epimorphism

`non_mf_groups_exist.tex`, the closing paragraph of
`\section{Prescribed MF quotients}`: the display `eq:closure-pullback`

`cl_MF^{W_Q}(N) = π_Q⁻¹( cl_MF^Q( π_Q(N) ) )`,

its justification — "an MF-target homomorphism from `W_Q` kills `N` exactly
when its unique factor through `Q` kills `π_Q(N)`" — the equivalence

`W_Q / N` is MF `↔` `ker π_Q ≤ N` and `Q / π_Q(N)` is MF,

and the observation `N = π_Q⁻¹(π_Q(N))` that the equivalence rests on.

## What is new here

The `W_Q` reading of this paragraph is already carried, at the development's
pullback closure operator `actualCoronaMFClosure`, by
`OneSidedMFRadical.manuscriptPrescribedQuotientRelationCalculus` in
`PrescribedQuotients.lean`, whose three clauses are
`MFCamouflage.actualCoronaMFClosure_eq_comap`,
`MFCamouflage.quotient_isCDEOperatorMF_iff` and `Subgroup.comap_map_eq_self`.
Those proofs are bespoke to the amalgam: they re-run
`MFCamouflage.factor_through_projection` by hand inside each corona.

This file does two things that development does not.

* It states the paragraph **for a general epimorphism**, not for `W_Q`.  The
  only input is the manuscript's own justification, isolated as
  `FactorsMFTargets φ`: precomposition with `φ` is a bijection
  `Hom(Q, T) ≃ Hom(G, T)` for every MF target `T`.  That is exactly
  `prop:universal-factorization` read one MF target at a time, and
  `factorsMFTargets_iff_ker_le` identifies it, for surjective `φ`, with the
  single containment `ker φ ≤ Rad_MF(G)`.
* It states the paragraph **at the printed closure** `literalMFClosure`, the
  manuscript's own `cl_MF^G(N) = ⋂ {ker f : N ≤ ker f, f : G → M, M MF}` from
  `LiteralMFClosure.lean`, rather than at the development's
  `actualCoronaMFClosure`.  Since the printed closure is literally an
  intersection over MF targets, the manuscript's one-line justification
  transcribes directly: `literalMFClosure_eq_comap_of_factors` is a target-by-
  target argument with no corona bookkeeping, and the forward inclusion needs
  no hypothesis on `φ` at all.

`camouflage_literalMFClosure_eq_comap` and
`camouflage_isCDEOperatorMF_quotient_iff` then specialize back to `W_Q`.

Contents:

* `FactorsMFTargets` — the universal-factorization hypothesis, one MF target
  at a time;
* `FactorsMFTargets.ker_le_actualCoronaMFResidual`,
  `factorsMFTargets_of_ker_le`, `factorsMFTargets_iff_ker_le` — it is the
  containment `ker φ ≤ Rad_MF(G)`;
* `literalMFClosure_eq_comap_of_factors` — `eq:closure-pullback`, general form;
* `comap_map_eq_self_of_ker_le` — the manuscript's "only additional
  observation";
* `isCDEOperatorMF_quotient_iff_of_factors` — the displayed equivalence;
* `manuscriptCoronaMFResidual_eq_comap_of_factors` — the sentence before it,
  as the case `N = ⊥`;
* `factorsMFTargets_projection`, `camouflage_literalMFClosure_eq_comap`,
  `camouflage_isCDEOperatorMF_quotient_iff`,
  `camouflage_manuscriptCoronaMFResidual_eq_comap` — the `W_Q` instance;
* `MFClosurePullbackAlongFactorization` — the four clauses as one closed
  `Prop`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace ClosurePullback

noncomputable section

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-! ## The universal-factorization hypothesis -/

/-- **`prop:universal-factorization`, one MF target at a time.**  A
homomorphism `φ : G → Q` *factors all MF targets* when precomposition with
`φ` is a bijection `Hom(Q, T) → Hom(G, T)` for every countable MF group `T`:
every homomorphism from `G` to an MF group is `f ∘ φ` for a unique
`f : Q → T`.

For the manuscript's `π_Q : W_Q → Q` this is exactly the conclusion of
`prop:universal-factorization`, whose hypothesis "every homomorphism from `B`
to an MF group is trivial" is supplied by `Rad_MF(B) = B`; see
`factorsMFTargets_projection`. -/
def FactorsMFTargets {G Q : Type} [Group G] [Group Q] (φ : G →* Q) : Prop :=
  ∀ (T : Type) [Group T] [Countable T], IsCDEOperatorMF T →
    Function.Bijective (fun f : Q →* T ↦ f.comp φ)

/-- A homomorphism that factors all MF targets has MF-invisible kernel: the
one target `G ⧸ Rad_MF(G)` already forces it. -/
theorem FactorsMFTargets.ker_le_actualCoronaMFResidual {G Q : Type} [Group G]
    [Group Q] [Countable G] {φ : G →* Q} (hφ : FactorsMFTargets φ) :
    φ.ker ≤ actualCoronaMFResidual G := by
  obtain ⟨f, hf⟩ :=
    (hφ (G ⧸ actualCoronaMFResidual G) actualCoronaMFQuotient_isCDEOperatorMF).2
      (QuotientGroup.mk' (actualCoronaMFResidual G))
  intro x hx
  have hval : f (φ x) = QuotientGroup.mk' (actualCoronaMFResidual G) x :=
    DFunLike.congr_fun hf x
  rw [MonoidHom.mem_ker.mp hx, map_one] at hval
  exact (QuotientGroup.eq_one_iff x).mp hval.symm

/-- Conversely, a surjection with MF-invisible kernel factors all MF targets:
an injective corona representation of the target turns any `g : G → T` into a
corona representation of `G`, which kills the kernel, so `g` descends. -/
theorem factorsMFTargets_of_ker_le {G Q : Type} [Group G] [Group Q]
    {φ : G →* Q} (hsurj : Function.Surjective φ)
    (hker : φ.ker ≤ actualCoronaMFResidual G) :
    FactorsMFTargets φ := by
  intro T _ _ hT
  obtain ⟨dims, hdims, -, j, hj⟩ := hT
  have hX : ∀ n, 0 < Fintype.card (naturalFiniteModel (dims n)) := by
    simpa using hdims
  constructor
  · intro f₁ f₂ h
    ext q
    obtain ⟨x, rfl⟩ := hsurj q
    exact DFunLike.congr_fun h x
  · intro g
    have hkerg : φ.ker ≤ g.ker := by
      intro x hx
      have hone := hker hx (fun n ↦ naturalFiniteModel (dims n)) hX (j.comp g)
      rw [MonoidHom.comp_apply] at hone
      exact MonoidHom.mem_ker.mpr (hj (hone.trans (map_one j).symm))
    exact ⟨φ.liftOfSurjective hsurj ⟨g, hkerg⟩,
      φ.liftOfRightInverse_comp _ _ _⟩

/-- For a surjection, factoring all MF targets *is* the containment
`ker φ ≤ Rad_MF(G)`. -/
theorem factorsMFTargets_iff_ker_le {G Q : Type} [Group G] [Group Q]
    [Countable G] {φ : G →* Q} (hsurj : Function.Surjective φ) :
    FactorsMFTargets φ ↔ φ.ker ≤ actualCoronaMFResidual G :=
  ⟨fun hφ ↦ hφ.ker_le_actualCoronaMFResidual,
    fun hker ↦ factorsMFTargets_of_ker_le hsurj hker⟩

/-! ## `eq:closure-pullback` -/

/-- **The display `eq:closure-pullback`, for a general epimorphism.**  For
every subgroup `N` of `G`,

`cl_MF^G(N) = φ⁻¹( cl_MF^Q( φ(N) ) )`,

with `cl_MF` the manuscript's printed intersection of MF-target kernels.

This is the manuscript's own one-line justification, transcribed.  For `⊆`,
an MF-target homomorphism `f : Q → T` killing `φ(N)` gives `f ∘ φ : G → T`
killing `N`, so `f ∘ φ` kills `cl_MF^G(N)`; no hypothesis on `φ` is used.
For `⊇`, an MF-target homomorphism `g : G → T` killing `N` is, by
`FactorsMFTargets`, the unique `f ∘ φ` for some `f : Q → T`, and that `f`
kills `φ(N)`; so `f` kills `cl_MF^Q(φ(N))`, and `g = f ∘ φ` kills its
preimage. -/
theorem literalMFClosure_eq_comap_of_factors {G Q : Type} [Group G] [Group Q]
    {φ : G →* Q} (hφ : FactorsMFTargets φ) (N : Subgroup G) :
    literalMFClosure G N = (literalMFClosure Q (N.map φ)).comap φ := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_comap.mpr ?_
    rw [mem_literalMFClosure_iff] at hx
    rw [mem_literalMFClosure_iff]
    intro T instT instC f hMF hNf
    have hsub : N ≤ (f.comp φ).ker := by
      intro y hy
      exact MonoidHom.mem_ker.mpr
        (MonoidHom.mem_ker.mp (hNf (Subgroup.mem_map_of_mem φ hy)))
    exact hx T instT instC (f.comp φ) hMF hsub
  · intro hx
    rw [Subgroup.mem_comap, mem_literalMFClosure_iff] at hx
    rw [mem_literalMFClosure_iff]
    intro T instT instC g hMF hNg
    obtain ⟨f, hf⟩ := (hφ T hMF).2 g
    have hval : ∀ y : G, f (φ y) = g y := fun y ↦ DFunLike.congr_fun hf y
    have hmap : N.map φ ≤ f.ker := by
      rintro _ ⟨y, hy, rfl⟩
      exact MonoidHom.mem_ker.mpr
        ((hval y).trans (MonoidHom.mem_ker.mp (hNg hy)))
    exact (hval x).symm.trans (hx T instT instC f hMF hmap)

/-- **The manuscript's "only additional observation".**  Once `ker φ ≤ N`, the
relation subgroup is recovered from its image: `N = φ⁻¹(φ(N))`. -/
theorem comap_map_eq_self_of_ker_le {G Q : Type} [Group G] [Group Q]
    {φ : G →* Q} {N : Subgroup G} (hker : φ.ker ≤ N) :
    (N.map φ).comap φ = N :=
  Subgroup.comap_map_eq_self hker

/-- **The displayed equivalence.**  `G / N` is MF exactly when `N` already
contains `ker φ` and the visible quotient `Q / φ(N)` is MF.

The proof is `prop:mf-residual-calculus`'s closure criterion — `G/N` is MF
precisely when `cl_MF^G(N) = N` — read through `eq:closure-pullback`.  Left to
right: `φ⁻¹(cl_MF^Q(φ(N))) = N` contains `ker φ` because `φ` sends it to
`1 ∈ cl_MF^Q(φ(N))`, and pushing the equality forward along the surjection
`φ` gives `cl_MF^Q(φ(N)) = φ(N)`.  Right to left is
`comap_map_eq_self_of_ker_le`. -/
theorem isCDEOperatorMF_quotient_iff_of_factors {G Q : Type} [Group G]
    [Group Q] [Countable G] [Countable Q] {φ : G →* Q}
    (hsurj : Function.Surjective φ) (hφ : FactorsMFTargets φ)
    (N : Subgroup G) [N.Normal] [(N.map φ).Normal] :
    IsCDEOperatorMF (G ⧸ N) ↔
      φ.ker ≤ N ∧ IsCDEOperatorMF (Q ⧸ N.map φ) := by
  constructor
  · intro hMF
    have hcomap : (literalMFClosure Q (N.map φ)).comap φ = N :=
      (literalMFClosure_eq_comap_of_factors hφ N).symm.trans
        ((isCDEOperatorMF_quotient_iff_literalMFClosure_eq N).mp hMF)
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [← hcomap]
      refine Subgroup.mem_comap.mpr ?_
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    · refine (isCDEOperatorMF_quotient_iff_literalMFClosure_eq
        (N.map φ)).mpr ?_
      have hmap := congrArg (fun K : Subgroup G ↦ K.map φ) hcomap
      simpa [Subgroup.map_comap_eq_self_of_surjective hsurj] using hmap
  · rintro ⟨hker, hMF⟩
    refine (isCDEOperatorMF_quotient_iff_literalMFClosure_eq N).mpr ?_
    rw [literalMFClosure_eq_comap_of_factors hφ N,
      (isCDEOperatorMF_quotient_iff_literalMFClosure_eq (N.map φ)).mp hMF]
    exact Subgroup.comap_map_eq_self hker

/-- **The sentence before the displayed equivalence**, as the case `N = ⊥` of
`eq:closure-pullback`: `Rad_MF(G) = φ⁻¹(Rad_MF(Q))`.  This uses the printed
identity `Rad_MF(G) = cl_MF^G(1)` at both ends. -/
theorem manuscriptCoronaMFResidual_eq_comap_of_factors {G Q : Type} [Group G]
    [Group Q] [Countable G] [Countable Q] {φ : G →* Q}
    (hφ : FactorsMFTargets φ) :
    manuscriptCoronaMFResidual G = (manuscriptCoronaMFResidual Q).comap φ := by
  have hbot : (⊥ : Subgroup G).map φ = ⊥ := by simp
  have h := literalMFClosure_eq_comap_of_factors hφ (⊥ : Subgroup G)
  rw [hbot, literalMFClosure_bot (G := G), literalMFClosure_bot (G := Q)] at h
  exact h

/-! ## The manuscript's instance: `φ = π_Q` -/

/-- **`prop:universal-factorization` supplies the hypothesis for `π_Q`.**
Every homomorphism from the black-hole vertex `B` to an MF group is trivial,
because `Rad_MF(B) = B` and MF groups embed in norm-matrix coronas; so
`prop:universal-factorization` applies to every MF target. -/
theorem factorsMFTargets_projection {B : Type} [Group B] (d : B) (Q : Type)
    [Group Q] (hfull : actualCoronaMFResidual B = ⊤) :
    FactorsMFTargets (MFCamouflage.projection d Q) := by
  intro T _ _ hT
  exact MFCamouflage.cdeMF_precomp_bijective d Q hfull hT

/-- **`eq:closure-pullback` as printed**, for `W_Q` and the printed closure. -/
theorem camouflage_literalMFClosure_eq_comap {B : Type} [Group B] (d : B)
    (Q : Type) [Group Q] (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (MFCamouflage.Camouflage d Q)) :
    literalMFClosure (MFCamouflage.Camouflage d Q) N =
      (literalMFClosure Q (N.map (MFCamouflage.projection d Q))).comap
        (MFCamouflage.projection d Q) :=
  literalMFClosure_eq_comap_of_factors (factorsMFTargets_projection d Q hfull) N

/-- **The displayed equivalence as printed**, for `W_Q`. -/
theorem camouflage_isCDEOperatorMF_quotient_iff {B : Type} [Group B]
    [Countable B] (d : B) (Q : Type) [Group Q] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (MFCamouflage.Camouflage d Q)) [N.Normal] :
    IsCDEOperatorMF (MFCamouflage.Camouflage d Q ⧸ N) ↔
      (MFCamouflage.projection d Q).ker ≤ N ∧
        IsCDEOperatorMF (Q ⧸ N.map (MFCamouflage.projection d Q)) :=
  isCDEOperatorMF_quotient_iff_of_factors
    (MFCamouflage.projection_surjective d Q)
    (factorsMFTargets_projection d Q hfull) N

/-- **`Rad_MF(W_Q) = π_Q⁻¹(Rad_MF(Q))`** at the printed radical, as the case
`N = ⊥`.  `manuscriptPrescribedMFQuotients` carries the same identity at the
development's radical `actualCoronaMFResidual`; the two radicals agree by
`manuscriptCoronaMFResidual_eq_actualCoronaMFResidual`. -/
theorem camouflage_manuscriptCoronaMFResidual_eq_comap {B : Type} [Group B]
    [Countable B] (d : B) (Q : Type) [Group Q] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤) :
    manuscriptCoronaMFResidual (MFCamouflage.Camouflage d Q) =
      (manuscriptCoronaMFResidual Q).comap (MFCamouflage.projection d Q) :=
  manuscriptCoronaMFResidual_eq_comap_of_factors
    (factorsMFTargets_projection d Q hfull)

/-! ## Manuscript wrapper -/

/-- **The closing paragraph of `\section{Prescribed MF quotients}`, for a
general epimorphism and at the printed MF closure.**  Let `φ : G ↠ Q` be a
surjection through which every homomorphism from `G` to an MF group factors
uniquely — the conclusion of `prop:universal-factorization` for `π_Q`.  Then,
for every normal `N ⊴ G`:

* `eq:closure-pullback`: `cl_MF^G(N) = φ⁻¹( cl_MF^Q( φ(N) ) )`;
* the case `N = ⊥`: `Rad_MF(G) = φ⁻¹( Rad_MF(Q) )`;
* the displayed equivalence: `G/N` is MF `↔` `ker φ ≤ N` and `Q/φ(N)` is MF;
* the observation it rests on: if `ker φ ≤ N` then `N = φ⁻¹(φ(N))`.

Both closures are the manuscript's printed intersection
`cl_MF^G(N) = ⋂ {ker f : N ≤ ker f, f : G → M, M MF}` of `literalMFClosure`,
and both radicals are the printed `Rad_MF` of `manuscriptCoronaMFResidual`.
The `W_Q` instance of the second and third clauses, at the development's
pullback closure operator, is `manuscriptPrescribedQuotientRelationCalculus`;
`camouflage_literalMFClosure_eq_comap` and
`camouflage_isCDEOperatorMF_quotient_iff` specialize this statement back to
`W_Q` at the printed closure. -/
def MFClosurePullbackAlongFactorization : Prop :=
  ∀ (G Q : Type) [Group G] [Group Q] [Countable G] [Countable Q]
    (φ : G →* Q), Function.Surjective φ → FactorsMFTargets φ →
      ∀ (N : Subgroup G) [N.Normal] [(N.map φ).Normal],
        literalMFClosure G N = (literalMFClosure Q (N.map φ)).comap φ ∧
          manuscriptCoronaMFResidual G =
            (manuscriptCoronaMFResidual Q).comap φ ∧
          (IsCDEOperatorMF (G ⧸ N) ↔
            φ.ker ≤ N ∧ IsCDEOperatorMF (Q ⧸ N.map φ)) ∧
          (φ.ker ≤ N → (N.map φ).comap φ = N)

/-- Closed proof of the general closure-pullback paragraph. -/
theorem manuscriptMFClosurePullbackAlongFactorization :
    MFClosurePullbackAlongFactorization := by
  intro G Q _ _ _ _ φ hsurj hφ N _ _
  exact ⟨literalMFClosure_eq_comap_of_factors hφ N,
    manuscriptCoronaMFResidual_eq_comap_of_factors hφ,
    isCDEOperatorMF_quotient_iff_of_factors hsurj hφ N,
    fun hker ↦ Subgroup.comap_map_eq_self hker⟩

end

end ClosurePullback
end OneSidedMFRadical
end Manuscript
end GroupApproximation
