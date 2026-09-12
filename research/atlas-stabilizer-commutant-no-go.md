---
rg: 2
id: atlas-stabilizer-commutant-no-go
kind: claim
title: No stabilizer-commutant deformation of the tensor flip meets the criterion, at any multiplicity
invalidates: [atlas-stabilizer-coset-witness]
distinct_from:
  atlas-stabilizer-slice-stationary: that is a first-order statement at one point (the flip) in one slice (`U(15)` at `k = 1`); this is a uniform positive lower bound over the entire commutant family at every multiplicity, and neither implies the other.
  atlas-true-criterion-baseline: that evaluates the objective at the classical warm starts and identifies the active set; this excludes an entire deformation family around one of them, for all `k`.
  leavitt-steinberg-hs-unstable: that is the open branch selection; this fences one lane of its search space and is evidence for neither branch.
  atlas-kernel-window-length-nine: that is a finite-quotient obstruction — short kernel words die under a retraction; this is an ultraproduct obstruction driven by quasisimplicity, and it kills a family of models rather than a range of words.
  block-monomial-coordinate-collapse: that collapses block-monomial models of the Kun--Thom wreath onto permutation models; this excludes stabilizer-commutant models of the Leavitt atlas by an exactly forced relation, with no monomiality hypothesis at all.
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
---

Let `P̄ = A₈ * A₈` be the canonical two-chart atlas source, `T_St` the usable
relator list of `atlas-steinberg-rank-five-translation`, and for
`U ∈ U(20160k)` let `π_U` be the exact criterion representation
(`π_U(h) = λ(h) ⊗ I_k` on the first chart, `U(λ(h) ⊗ I_k)U*` on the second).
Under `A₈ ≅ GL₄(𝔽₂)` let `M < A₈` be the stabilizer of a nonzero vector of
`𝔽₂⁴`, of order `1344` and index `15`, and let `J` be the tensor flip.

**Theorem.**

```text
inf { max_{s ∈ T_St} ‖π_{DJ}(s) − I‖₂  :  k ≥ 1,  D ∈ π₁(M)′ }  >  0 ,
```

where `π₁(M)′` is the commutant of the first chart's copy of `M` on
`ℓ²(A₈) ⊗ ℂ^k ≅ ℓ²(M) ⊗ ℂ^{15k}`.  In particular the whole Stage-1 family
`D ∈ I_{ℓ²(M)} ⊗ U(15k)` is excluded — at every multiplicity, with no
monomiality, bounded-complexity, proximity-to-`I` or finite-order hypothesis
on `D`.

The mechanism is that the family forces an exact relation the target does not
satisfy.  `D` commutes with `π₁(m)` for `m ∈ M` by construction, and
`J L_b J* = R_b` commutes with every left translation, so
`[π₁(m), π₂(b)] = 1` holds **exactly**, for all `m ∈ M` and `b ∈ A₈`, in every
member of the family.  The first-chart transvection `p₀₁ = I + E₀₁` fixes the
stabilized vector, hence lies in `M`, so `c = [p¹₀₁, p²₁₀]` — free-product
length four — is killed exactly by every such model, while the repository's
binary-Leavitt normal-form evaluator returns `leavitt_is_one = False` for it
(12 surviving monomials): `c` has nontrivial image in `Q`.  Quasisimplicity of
`E = P̄/⟨⟨T_St⟩⟩` (`atlas-relator-central-sufficiency`) then makes a
defect-vanishing sequence impossible, since the induced ultraproduct
homomorphism would be nontrivial with a noncentral element in its kernel.

**Scope, stated sharply because it is easy to overclaim.**  This is a
statement about one structured search family, not about the criterion.  It
does not bound `d_k = min_{U ∈ U(20160k)} max_s ‖π_U(s) − I‖₂` away from zero
for unrestricted `U`, and therefore is evidence for neither branch of
`leavitt-steinberg-hs-stability-fork`.  What it removes is the cheapest lane —
the one the campaign design put first — and the temptation to read the flat
Stage-1 pilot as "needs more iterations".

**The reusable screen.**  The proof used only that the family forces *some*
exact relation with nontrivial image in `Q`; the shape of `D` never entered.
So: any structured atlas ansatz that accidentally enforces a relation of `P̄`
surviving to `Q` is globally excluded at every multiplicity, by quasisimplicity
of `E` together with `Z(Q) = 1`.  Enumerating the relations an ansatz forces
and evaluating them in the Leavitt normal form is a cheap test that should
precede any optimization spend — and it is the reason the exact normal-form
evaluator, built for the kernel-window work, keeps paying rent.

Recorded 2026-08-16 from an external full-corpus audit; the argument is
re-derived in `research/artifacts/hyperlinear-q34-audit-2026-08-16.md` §(e),
including the free strengthening from `I_{ℓ²(M)} ⊗ U(15k)` to the full
commutant `π₁(M)′`.
