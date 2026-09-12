---
rg: 2
id: stw22-extreme-traces-detect-the-norm-fibre-gap-proof
kind: route
title: Send extreme traces to norm fibres and compare their trace-kernel quotients
target: stw22-norm-fibre-gap-is-the-trace-obstruction
requires: []
artifacts:
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
---

First note `J_x subset K_x`: if `f(x)=0`, then

```text
tau_x((fa)*(fa))=|f(x)|^2 tau_x(a*a)=0,
```

and closedness gives the inclusion.

Assume condition 2 and let `phi` be an extreme tracial state on `M`.  Its
GNS von Neumann algebra is a factor.  Since `C(X)` is central in `M`, its
image in that factor is scalar, so `phi|C(X)=ev_x` for some `x`.  For
`f(x)=0`, Cauchy--Schwarz gives

```text
|phi(fa)|^2<=phi(|f|^2)phi(a*a)=0.
```

Thus `phi` vanishes on `J_x` and defines a trace on `M/J_x`.  Condition 2
makes it vanish on `K_x/J_x`; it factors through `M_x`.  The unique-trace
hypothesis on `M_x` now gives `phi=tau_x`.

Every extreme point of `T(M)` is therefore one of the `tau_x`.  By
Krein--Milman, every trace belongs to their closed convex hull.  The map

```text
Prob(X)->T(M),                 mu |-> mu o E
```

is weak-star continuous, affine, and injective because it restricts to the
usual integration map on `C(X)`.  Its compact image contains every finite
convex combination of the `tau_x`, hence their closed convex hull.  It is
therefore all of `T(M)`, proving condition 1.

Condition 1 immediately implies condition 2.  Pull a trace on `M/J_x` back
to `M`.  Its restriction to `C(X)` is `ev_x`, so the representing measure in
condition 1 is `delta_x`; the pullback equals `tau_x` and annihilates `K_x`.

Finally, because `M_x=(M/J_x)/(K_x/J_x)` has a unique trace, condition 2 is
equivalent to condition 3.  This proves all equivalences.

For `M=C(X) tensor M_0` with `M_0` a finite factor, faithfulness of its trace
gives

```text
K_x={a:a(x)=0}=J_x,
```

which proves the stated positive example.  Uniform `2`-norm completion alone
controls `K_x`, not equality with the C*-norm ideal `J_x`; this is precisely
the gap a fibrewise disintegration argument cannot cross.
