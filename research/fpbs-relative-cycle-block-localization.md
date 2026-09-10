---
rg: 2
id: fpbs-relative-cycle-block-localization
kind: claim
title: Near-optimal source graphings admit weighted boundary localization of their relative cycle surplus
distinct_from:
  fpbs-bernoulli-cycle-tail-compactness: that controls the entire cycle dimension of Bernoulli minimizers and implies cost--Betti equality; this controls only the relative projection across a specified factor
  fpbs-correlated-reuse-flags-removable: that asks for vanishing conditional traffic defect; this asks for an explicit block-boundary estimate on relative cycle operators and uses a different connected rounding construction
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

**OPEN.** For every free p.m.p. factor pi:Y->X of an infinite finitely
generated group, find finite-label generating source graphings Phi_n
with c(Phi_n)->C(Y). Let H_n be their conditional-support base graphings,
K_n their relative cycle operators, and d_n a degree bound for H_n.
Find measurable partitions E_n into H_n-connected blocks of size at
most M_n such that, writing P_out,n for the crossing-edge projection,

    (1+2 d_n M_n^2) Tr(P_out,n K_n) -> 0.

## Attempts

`fpbs-sparse-base-connected-cycle-rounding` now gives an alternative
connected surgery when the relative certificate is supported on a
sufficiently sparse base region with a fixed finite label set, for an
exact group and Bernoulli base. It uses a base-measurable separator from
Fraczyk plus Lovasz, and pays actual cut rank rather than M^2 times
boundary trace. The required sparse support does not follow from this
node's premise or from rarity of source reuse flags. It is not a proof
of this universal localization assertion.

Impose a common finite-block forest at the cost infimum. Section 5 of
the artifact justifies this without a finite normal subgroup, but
proves that a potential cost gap scales as D=q D_A under contraction.
It supplies neither this weighted boundary estimate nor the required
finite-label presentations.

Use determinantal rounding of K_n. This can disconnect even for a
finite extension with a source treeing. The replacement in Section 6
does preserve connectivity, but only yields a small error when the
displayed localization estimate holds. Merely taking larger blocks or
showing their weighted boundary tends to zero omits the factor M_n^2.

No universal construction establishing this premise is known here.
For the fixed source treeing on F_r x C_M in Section 2, Section 6
proves Tr(P_out K)>=(r-1)/4 for every finite-block partition: every
edge lies on a square and horizontal tree expansion forces a positive
boundary density. Thus varying the source graphings is essential;
searching only for better partitions of that fixed certificate fails
even in this known fixed-price family.

Section 6 explains its equivalence to factor-cost preservation in
the finitely generated setting. That equivalence is a reformulation,
not evidence that the premise is established.
