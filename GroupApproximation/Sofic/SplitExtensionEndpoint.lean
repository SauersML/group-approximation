import GroupApproximation.Algebra.SplitExtensionFailure
import GroupApproximation.Sofic.AscendingHNNWreathWitness
import GroupApproximation.Sofic.CDEOperatorMF

/-!
# Theorem 54.2 with its middle-group hypothesis discharged

`Algebra/SplitExtensionFailure` proves Theorem 54.2 in the shape the dossier
argues it: both ends of the split extension `1 → K^{(X)} → K^{(X)} ⋊ G → G → 1`
are as tame as one could ask -- the kernel is locally finite, amenable,
residually finite, linear and operator-MF, and the quotient is a copy of the
acting group -- while failure at the *middle* enters as a hypothesis `hW`, since
no witness for it lives in that file.

The witness does live in the repository.  Theorem 34.4
(`not_isCDEOperatorMF_wreath`) produces a permutational wreath product that is
not MF from a property-`(T)` group with a proper injective self-embedding, with
no soficity, residual finiteness or finite-index hypothesis; and
`isCDEOperatorMF_iff_isOperatorMF` identifies the two MF predicates for a
countable group.  Feeding one into the other discharges `hW` and turns Theorem
54.2 from a conditional into a theorem about a construction the repository
actually builds.

What is left as a hypothesis is `IsOperatorMF (Vertical β hβ)`, i.e. tameness of
the *acting* group.  That is not a defect of the argument but its content: the
whole point of 54.2 is that a tame kernel and a tame quotient do not make a tame
middle, so both ends must be assumed tame for the statement to say anything.  In
the dossier's family the acting group is residually finite, which is strictly
stronger.
-/

namespace GroupApproximation

namespace MarkedCompression

open SemidirectProduct MappingTelescope

section Endpoint

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

include hβ in
/-- The middle group of the ascending-HNN split extension is not operator-MF.
This is Theorem 34.4 read through `isCDEOperatorMF_iff_isOperatorMF`. -/
theorem not_isOperatorMF_wreath
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    {k₀ : K₀} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) :
    ¬ IsOperatorMF (WreathV (K := K₀) β hβ) := fun hcon =>
  not_isCDEOperatorMF_wreath β hβ hΓ hk₀ hk2 ha₀
    ((isCDEOperatorMF_iff_isOperatorMF _).mpr hcon)

include hβ in
/-- **Theorem 54.2 for MF, with the middle-group hypothesis discharged.**  Over
a property-`(T)` group with a proper injective self-embedding and an operator-MF
ascending-HNN extension, the split extension whose kernel is a finite lamp group
over the coset space has

* an operator-MF kernel (it is a copy of the lamp group, residually finite);
* an operator-MF quotient (it is a copy of the acting group);
* a middle group that is **not** operator-MF.

So operator-MF is not closed under split extensions, even with a locally finite,
amenable, residually finite, linear kernel -- and the failure is exhibited, not
assumed. -/
theorem mf_not_closed_under_split_extension_hnn
    [Finite K₀] [Countable (Cosets β hβ)]
    [Countable (WreathV (K := K₀) β hβ)]
    (hMF : IsOperatorMF (Vertical β hβ))
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    {k₀ : K₀} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) :
    IsOperatorMF
        ((rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ).ker) ∧
      IsOperatorMF (WreathV (K := K₀) β hβ ⧸
        (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ).ker) ∧
      ¬ IsOperatorMF (WreathV (K := K₀) β hβ) :=
  ⟨SplitExtensionFailure.ker_isOperatorMF,
    hMF.comap (QuotientGroup.kerLift _) (QuotientGroup.kerLift_injective _),
    not_isOperatorMF_wreath β hβ hΓ hk₀ hk2 ha₀⟩

end Endpoint

end MarkedCompression

end GroupApproximation
