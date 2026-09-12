---
rg: 2
id: finite-clifford-symplectic-section-obstruction-citation
kind: route
title: Import Galindo's splitting criterion and evaluate it at the binary blocks
target: finite-clifford-symplectic-section-obstruction
requires: []
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

Citation import plus one divisibility check, not a reproof.

The splitting criterion is Galindo, *Splitting of Clifford groups associated
to finite abelian groups*, `arXiv:2603.24743`, v2 11 Aug 2026: the extension
`1 → V_A → C(A) → Sp(V_A) → 1` splits as a semidirect product if and only if
`4 ∤ |A|`, with the obstruction controlled entirely by the 2-primary
component, vanishing exactly when that component is trivial or cyclic of
order two.  The abstract page was read on 2026-08-18 and the statement
recorded verbatim in
`research/artifacts/hyperlinear-q34-literature-2026-08-18.md`; the body was
not read, and this route asserts only that the cited theorem says what is
recorded there.  Korbelář--Tolar, `arXiv:2606.08215`, state the same
threshold for `ℤ_{n_1} ⊕ ⋯ ⊕ ℤ_{n_k}` and are recorded as independent
confirmation of the criterion, not as a second proof of it.

**Evaluation at the blocks in play.**  `vertex-supported-symplectic-completion`
produces nondegenerate binary symplectic spaces `W` of even dimension `2n`,
represented on `n` qubits, i.e. `A = (ℤ/2)^n` and `V_A = A ⊕ Â ≅ W`.  Then
`|A| = 2^n`, and `4 | 2^n` exactly when `n ≥ 2`.  So the extension splits for
`n = 1` and is nonsplit for every `n ≥ 2`, which is the claim.  A splitting
is by definition a multiplicative section, so nonsplitness is exactly the
nonexistence of a homomorphism `Sp(V_A) → C(A)` over the projection.

**Trust surface.**  This route imports a 2026 preprint that the corpus has
not verified beyond its abstract.  Nothing downstream of it is asserted
unconditionally: it is used only to rule *out* a design (a universal
multiplicative lift), so a failure of the citation would restore an option
rather than falsify a positive result.  No route to `q3-4-resolved` requires
it.
