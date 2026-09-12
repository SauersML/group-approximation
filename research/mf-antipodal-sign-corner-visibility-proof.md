---
rg: 2
id: mf-antipodal-sign-corner-visibility-proof
kind: route
title: Cut the sign corner, then apply the antipodal certificate
target: mf-antipodal-sign-corner-visibility
requires: [countable-group-mf-conventions, hyperlinear-elementwise-visibility]
artifacts:
  - GroupApproximation/Sofic/AntipodalTraceExtraction.lean
  - notes/TRUE_ANTIPODAL_TRACE_EXTRACTION.md
---

## Why sufficient

**The corner.**  By `countable-group-mf-conventions`, MF gives a faithful
homomorphism `u : G -> U(Q)` into a matrix corona.  Since `z` is central of
order `2` and `u` is injective, `u(z)` is a self-adjoint unitary different
from `1` commuting with `u(G)`, so

```text
P = (1-u(z))/2 != 0,   u(a) P u(a)^* = P  (a in G),   P u(z) = -P.
```

`P` lifts to projections `p_n` (a self-adjoint lift is asymptotically
idempotent, so continuous functional calculus applies), nonzero along an
infinite index set, and `PQP` is the corona of the corners `M_(r_n)` with
`r_n = rank(p_n) >= 1`.  Reading `countable-group-mf-conventions` in the other
direction, the homomorphism `a |-> P u(a)` is carried by operator-norm local
models `v_n : G -> U(r_n)` with defect tending to `0` on every finite set,
and `v_n(z) -> -1` in operator norm.

**The antipodal defect.**  Apply `(A1)`.  Asymptotic multiplicativity gives

```text
v_n(s) v_n(g) v_n(s)^* - v_n(z g) -> 0,
v_n(z g) - v_n(z) v_n(g) -> 0,
v_n(z) v_n(g) + v_n(g) -> 0,
```

in operator norm, hence in `||.||_(2,norm)`.  So the antipodal defect
`||v_n(s)v_n(g)v_n(s)^* + v_n(g)||_(2,norm)` tends to `0`.

**Trace extraction.**  The formalized certificate
`4 |tr_(r_n)(v_n(g))|^2 <= ||v_n(s)v_n(g)v_n(s)^* + v_n(g)||_(2,norm)^2`
(`AntipodalTraceExtraction`, quantitative sequential form) then gives
`tr_(r_n)(v_n(g)) -> 0`, so
`||v_n(g)-1||_(2,norm)^2 = 2-2 Re tr_(r_n)(v_n(g)) -> 2`.  Discarding finitely
many indices gives tracial visibility with `c_g = 1`, a constant independent
of the finite set and the tolerance.

**The consequence.**  Elements in a finite normal subgroup are visible by
`mf-finite-normal-tracially-visible`; elements with nontrivial image in a
hyperlinear quotient are visible by pullback; `z`-antipodal elements are
visible by the above.  If these exhaust `G\{1}`, then
`hyperlinear-elementwise-visibility` makes `G` hyperlinear.  End proof.

## Note for the non-MF side

The same computation read contrapositively is a *consistency check* on the
central-sign architecture, not a threat to it: there the conclusion is that no
corona model detects the mark at all, so no sign corner exists and nothing is
extracted.  Where a sign corner does exist --- i.e. where the group is MF ---
antipodal relations are automatically tracially visible.
