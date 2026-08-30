---
rg: 2
id: stw22-identify-multiframes-and-detect-determinant-loop-proof
kind: route
title: Collapse an orthogonal frame to one partial isometry and retain the determinant winding
target: stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
requires: []
artifacts:
  - research/artifacts/stw22-arbitrary-factor-stiefel-boundary-audit-2026-08-30.md
---

Fix the base frame `(s_j)` and let `(t_j)` be another exact frame.  Define

```text
V=sum_j t_js_j^*.
```

Orthogonality gives

```text
V^*V=sum_(j,k)s_jt_j^*t_ks_k^*=sum_j s_js_j^*=q.
```

Conversely, if `V^*V=q`, then `t_j=Vs_j` satisfies

```text
t_j^*t_k=s_j^*qs_k=delta_(jk)p.
```

The two constructions are inverse.  For two frames `(t_j)` and `(t'_j)`,
cyclicity of the trace and `s_k^*s_j=0` for `j!=k` give

```text
||V-V'||_2^2=sum_j ||t_j-t'_j||_2^2.                  (SB1)
```

Thus this is an isometry for the Hilbert-sum metric.  The elementary
comparison of the Euclidean and maximum norms on `m` coordinates gives the
recorded bi-Lipschitz constants.  Extending a partial isometry with initial
projection `q` to a unitary identifies the same space with
`U(N)/(q+U((1-q)N(1-q)))`.

For the obstruction, equip `M_n` with normalized trace and put

```text
ell_n(z)=diag(z,1,...,1),       z in S^1.
```

Then

```text
||ell_n(z)-1||_2=|z-1|/sqrt(n)<=2/sqrt(n).             (SB2)
```

But `det o ell_n:S^1->S^1` is the identity map, of degree one.  Therefore
`ell_n` is not null-homotopic in `U(n)`.  Given any proposed uniform local
loop-filling radius `delta`, choose `n` with `2/sqrt(n)<delta`; `(SB2)` is a
loop inside that ball which has no filling even in the entire fibre.  This
proves failure of factor-uniform equi-`LC^1` without strict slack.

When `rank(q)<n`, the fibration

```text
U(n-rank(q)) -> U(n) -> St_(M_n)(q)
```

has an isomorphism on fundamental groups at the left: the standard block
inclusion sends the determinant generator to the determinant generator.
The long exact homotopy sequence therefore makes the Stiefel space simply
connected.  Positive slack removes the elementary topological obstruction,
leaving the uniform metric filling estimate as the exact unresolved hinge.
