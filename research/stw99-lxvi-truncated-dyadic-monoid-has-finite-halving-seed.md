---
rg: 2
id: stw99-lxvi-truncated-dyadic-monoid-has-finite-halving-seed
kind: claim
title: A simple conical monoid realizes the full finite dyadic seed and the sharp LXVI perforation ladder
distinct_from:
  stw99-lxvi-mixed-algebra-with-dyadic-finite-projection: that asks for a C-star algebra realizing the configuration; this is an abstract projection-monoid consistency model and makes no C-star realizability claim.
  triangular-hopf-bundles-admit-coherent-dyadic-euler-roots: that builds finite-depth vector-bundle triangles with nonzero Euler classes; this gives one infinite coherent chain in a simple conical monoid but has no bundle or analytic dynamics.
artifacts:
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

**ESTABLISHED ALGEBRAIC CONSISTENCY MODEL.**  Put

```text
M={r in Z[1/2] : 0<=r<=1},       r plus_M s=min(1,r+s).                    (TDM1)
```

Then `M` is a countable conical commutative monoid with the following
properties.

1. `M` is simple: every nonzero element generates all of `M` as an order
   ideal.
2. `u=1` is properly infinite, since `u plus_M u=u`.
3. `p=1/2` is finite: `p plus_M y=p` forces `y=0`.
4. With `x_n=2^(-(n+1))`,

   ```text
   x_0=p,                    x_n=2x_(n+1)  for every n.                    (TDM2)
   ```

5. Every `x_n` is finite and full, and the least integer `m_n` satisfying
   `u<=m_n x_n` is

   ```text
   m_n=2^(n+1)>2^n,          m_n x_n=u,          u not<=x_n.               (TDM3)
   ```

Thus the exact coherent dyadic chain required by LXVI, a finite seed whose
double is properly infinite, simplicity/fullness, and the unbounded
comparison coefficients forced by
`stw99-lxvi-car-forces-unbounded-cu-perforation` are mutually consistent at
the level of a bare projection monoid; (TDM3) even attains the smallest
possible dyadic threshold.

This does **not** construct an LXVI witness.  In particular, no claim is made
that `M` is `V(B)` for a simple C-star algebra.  The result is a no-go for a
purely formal contradiction from conicality, simplicity, finiteness, dyadic
divisibility, or the already-known perforation ladder alone.  Any
impossibility proof must use an additional C-star realizability constraint;
any construction must realize this type of noncancellative order without
triggering the analytic Rordam no-gos.
