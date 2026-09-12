---
rg: 2
id: atlas-three-label-mode-two-unitary-moment-reduction
kind: claim
title: Three controlled Atlas label modes reduce exactly to two noncommutative unitary moment variables
distinct_from:
  atlas-outer-involution-two-sector-collapses-to-one-unitary: that proves two outer spectral sectors leave one commutative coefficient unitary and are impossible; this identifies the first controlled-label architecture capable of full growing coefficient algebras and writes every literal defect exactly.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that gives the abstract double-commutant invariance of arbitrary relative unitaries; this chooses an explicit outer-aware three-projection slice and computes its complete finite word objective after quotienting the gauge.
  atlas-square-root-bridge-two-matrix-rank-reduction: that produces thirteen binary rank polynomials in two arbitrary matrices on one q14 frame; this produces complex normalized-HS trace-moment polynomials in two unitaries for the canonical regular-A8 criterion.
---

**ESTABLISHED EXACT REDUCTION.**  Let `W` implement an outer involution of
`A8` on `l2(A8)`, put `P_plus=(I+W)/2`, `P_minus=(I-W)/2`, and let `E` be
the rank-one projection onto `delta_1`.  Since `W delta_1=delta_1`,

```text
P_0=E,       P_1=P_plus-E,       P_2=P_minus          (TLM1)
```

are three nonzero orthogonal label projections summing to the identity.
For arbitrary `V_0,V_1,V_2 in U(r)`, put

```text
U=sum_(j=0)^2 P_j tensor V_j.                         (TLM2)
```

This is an exact relative unitary.  Right chart-commutant gauge reduces it
without changing the represented second chart to

```text
U_Z=sum_(j=0)^2 P_j tensor Z_j,
Z_0=I,       Z_1=V_1 V_0^*,       Z_2=V_2 V_0^*.     (TLM3)
```

Let a literal free-product word be written

```text
s=a_0 b_1 a_1 ... b_l a_l,
a_t in A8_1,       b_t in A8_2.                       (TLM4)
```

For multi-indices `i=(i_1,...,i_l)` and `j=(j_1,...,j_l)` in
`{0,1,2}^l`, define

```text
C_s(i,j)=lambda(a_0)
           product_(t=1)^l
             (P_(i_t) lambda(b_t) P_(j_t) lambda(a_t)),
M_s(i,j)=product_(t=1)^l Z_(i_t) Z_(j_t)^*,
c_s(i,j)=tr_(20160)(C_s(i,j)).                        (TLM5)
```

Then the operator and normalized-HS defect equations are exactly

```text
pi_(U_Z)(s)=sum_(i,j) C_s(i,j) tensor M_s(i,j),       (TLM6)

||pi_(U_Z)(s)-I||_2^2
 =2-2 Re sum_(i,j) c_s(i,j) tr_r(M_s(i,j)).           (TLM7)
```

Thus the entire fixed literal Atlas packet restricts on `(TLM2)` to one
finite affine system in tracial moments of **two** unitary variables.  The
coefficients `c_s(i,j)` are fixed explicit algebraic numbers computed only
from `20160 by 20160` label matrices; no matrix dimension or coefficient
unknown remains in them.

The reduction is genuinely full-coefficient.  The three matrices `P_j` are
linearly independent, so the span of the `A8 by A8` block coefficients of
`U_Z` contains `I,Z_1,Z_2`.  Consequently

```text
D(U_Z)=C*(Z_1,Z_2).                                   (TLM8)
```

Choosing `Z_1,Z_2` to generate `M_r(C)` therefore meets the purified full-
coefficient requirement.  Three is minimal inside controlled-label models:
after gauge, two modes leave only one unitary and hence a commutative
coefficient algebra, whereas three modes leave two unitaries which may
generate `M_r(C)` with macroscopic commutator.

This is a reduction, not a positive certificate.  The remaining constructive
problem on this slice is to find growing full-matrix pairs `(Z_1,Z_2)` whose
finite moment vector in `(TLM7)` approaches the all-ones Atlas target.

DERIVATION
atlas-three-label-mode-moment-formula-proof
