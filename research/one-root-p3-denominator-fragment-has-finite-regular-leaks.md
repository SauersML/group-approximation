---
rg: 2
id: one-root-p3-denominator-fragment-has-finite-regular-leaks
kind: claim
title: One p-three root-scaling relation has exact finite regular centralizer leaks
distinct_from:
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies exact packets for a different Baumslag--Solitar exponent and studies a cyclic wrapper; this gives the minimal arithmetic root-fragment countermodel consumed by the SL3 denominator audit.
  source-hecke-data-leave-projective-square-free: that leaves a scalar coefficient free in abstract tracial extensions; this constructs exact finite-dimensional regular-character models of one native root relation.
  sl3-noncorrectable-lambda-sector-has-no-projective-leak: that is the full six-root arithmetic statement; this proves that no proof can use just one root-scaling relation at a time.
---

Consider the root-denominator fragment

```text
P=<a,h,t | h a h^(-1)=a^9, [t,a]=1>.                 (RLF1)
```

There is a sequence of exact finite-dimensional representations of `(RLF1)`
whose restriction to `<a,h> ~= BS(1,9)` has asymptotically regular
character, while

```text
1-|tr([t,h])|^2 -> 1.                                 (RLF2)
```

Indeed `BS(1,9)` is residually finite.  Choose finite quotients `Q_n` that
are injective on an increasing sequence of word balls, and let `lambda_n`
be their left-regular representations.  Define

```text
rho_n(a)=lambda_n(a),
rho_n(h)=lambda_n(h),
rho_n(t)=lambda_n(a).                                  (RLF3)
```

Both relators in `(RLF1)` hold exactly.  Every fixed nonidentity word of
`BS(1,9)` eventually has normalized trace zero.  The word
`[t,h]=[a,h]` is nontrivial in `BS(1,9)`, so its trace is eventually zero,
proving `(RLF2)`.

For the arithmetic pair, take `a=e_13(1)` and
`h=diag(3,1,1/3)`; then `hah^(-1)=e_13(9)=a^9`.  Thus the strongest possible
canonical trace tests and exact normalized-HS control on this one root
relation do not transfer centrality from `a` to `h`.  The same construction
applies to every individual expanded root after reversing `h` when needed.
Any successful direct proof must use genuinely joint incidence among
multiple noncommuting roots.
