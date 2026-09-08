---
rg: 2
id: one-almost-abelian-iwahori-vertex-has-linear-capture
kind: claim
title: A nearly commuting first modular vertex gives explicit linear Iwahori capture in every Schatten norm
distinct_from:
  commuting-iwahori-pairs-have-quadratic-rank-repair: that assumes all four generators commute jointly and changes the joint defect support; this requires only a small first-vertex commutator and constructs a cyclic endpoint without a reducing projection.
  iwahori-spectral-residual-gate-has-polynomial-step: that assumes a low-singular-residual condition and a small operator residual; this uses a finite word calculation and spectral rounding without either hypothesis.
  iwahori-local-global-defect-question: that asks for capture for every small-defect input; this gives a linear estimate with an additional first-vertex commutator term, which need not be small at arbitrary compatible representations.
artifacts:
  - research/artifacts/one-vertex-abelian-iwahori-capture-2026-09-08.md
---

Let `S_i,B_i` be two exact modular vertex representations in the same
dimension: `S_i^4=I`, `S_i^2=B_i^3`. Put

```text
T_i=S_i^(-1)B_i,             L_i=S_i B_i^(-1),
a_p=||T_1-T_2^2||_p,
b_p=||L_1^2-L_2||_p,
k_p=||S_1B_1-B_1S_1||_p.
```

Use normalized Schatten norms `1<=p<infinity` and the operator norm
for `p=infinity`. Let `C` be obtained by rounding the spectrum of
`T_2` to nearest cube roots of unity, with a fixed choice at ties.
Then the single endpoint

```text
(S_1',B_1',S_2',B_2')=(I,C^2,I,C)
```

is exactly Iwahori compatible in the original dimension and satisfies,
simultaneously for every such `p`,

```text
max_U ||U'-U||_p <= 249(a_p+k_p)+(141/2)b_p
                 <= 320(max(a_p,b_p)+k_p).
```

The central edge residual and all cross-vertex commutators are absent
from the hypotheses. No smallness assumption is needed for the displayed
inequality. In particular, if the first vertex commutes exactly, small
Iwahori defect alone gives linear same-dimensional repair for this class.

The proof forces `T_2` approximately to have orders fifteen and
twenty-four, then order three by a Bezout identity. This makes both
`S_i` close to the identity and permits the explicit spectral rounding.
The result provides neither a rank bound on the entire correction nor
a bound on `k_p` from arbitrary Iwahori defect. Nonabelian compatible
endpoints need not have a small first-vertex commutator, so the general
flexible capture question remains open.
