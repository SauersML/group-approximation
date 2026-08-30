---
rg: 2
id: stw22-norm-fibre-gap-is-the-trace-obstruction
kind: claim
title: The gap between norm fibres and 2-norm fibres is exactly the Bauer trace obstruction
distinct_from:
  stw99-problem-xxii-tracial-completion-traces: that asks for automatic continuity in every uniform tracial completion; this gives an exact criterion for a compact tracial C(X)-bundle with unique-trace 2-norm fibres.
artifacts:
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
---

Let `X` be compact Hausdorff and let `M` be a unital C*-algebra containing
`C(X)` centrally.  Suppose there is a unital tracial conditional expectation

```text
E:M->C(X)
```

such that, for every `x in X`, the trace `tau_x=ev_x o E` has a unique-trace
factor quotient

```text
M_x=M/K_x,             K_x={a:tau_x(a*a)=0}.
```

Put

```text
J_x=closure(C_0(X\{x})M) subset K_x.
```

Then the following are equivalent:

1. every tracial state on `M` equals `mu o E` for a unique probability
   measure `mu` on `X`;
2. for every `x`, every tracial state on the C*-norm fibre `M/J_x`
   annihilates `K_x/J_x`;
3. every C*-norm fibre `M/J_x` has the unique tracial state induced by
   `tau_x`.

Consequently automatic trace continuity holds whenever `J_x=K_x` for all
`x`.  The condition holds for the norm-continuous trivial field
`C(X) tensor M_0` when `M_0` is a finite factor, but it need not follow from
uniform `2`-norm completeness.  The quotient

```text
K_x/J_x
```

is the exact location where a singular trace supported at one fibre can
hide.
