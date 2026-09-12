---
rg: 2
id: stw01-arbitrary-extension-net-splitting-proof
kind: route
title: Turn an arbitrary approximate-unit net into a central projection in a cofinal quasitracial quotient
target: stw01-extensions-preserve-qt-linearity
requires: []
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Fix a bounded `2`-quasitrace `tau` on `A` and put `theta=tau|I`.  The ideal
hypothesis makes `theta` a bounded trace.  Let `(e_lambda)_(lambda in Lambda)`
be any positive-contractive approximate-unit net for `I`.  The bounded trace
has its canonical finite tracial extension `tilde(theta)` to `M(I)`, and

```text
theta(e_lambda), theta(e_lambda^2) -> ||theta||.            (AEN1)
```

Indeed both `(e_lambda)` and `(e_lambda^2)` are approximate units, and a
positive functional converges to its norm along every positive-contractive
approximate unit.  Since

```text
0 <= (e_lambda-e_lambda^2)^2 <= e_lambda-e_lambda^2,
```

linearity of `theta` gives

```text
tau((e_lambda-e_lambda^2)^2) -> 0.                           (AEN2)
```

Every `a in A` acts as a multiplier of `I`.  Put `r_lambda=1-e_lambda` in
`M(I)`.  From `(AEN1)`,

```text
tilde(theta)(r_lambda^2)
 = ||theta||-2theta(e_lambda)+theta(e_lambda^2) -> 0.
```

The tracial `2`-seminorm and its triangle inequality therefore give

```text
||[e_lambda,a]||_(2,tilde(theta))
 <= 2||a|| tilde(theta)(r_lambda^2)^(1/2) -> 0.              (AEN3)
```

Because the commutator belongs to `I`, `(AEN3)` is exactly convergence of
`tau([e_lambda,a]*[e_lambda,a])` to zero.

Choose an ultrafilter `omega` on `Lambda` which contains every tail
`{mu:mu>=lambda}`; the tails have the finite-intersection property.  On
`ell_infinity(Lambda,A)` define the coordinate ultralimit quasitrace

```text
tau_omega((x_lambda))=lim_omega tau(x_lambda)
```

and factor by its square-null ideal.  If `q` is the class of `(e_lambda)`,
then `(AEN2)` makes `q` a projection and `(AEN3)` makes it commute with the
constant copy `iota(A)`.  Hence

```text
theta_0(a)=q iota(a),             theta_1(a)=(1-q)iota(a)
```

are star homomorphisms into orthogonal corners.

The tail homomorphism kills `I`, because `(1-e_lambda)i->0` in norm for
every `i in I`; its induced bounded quasitrace therefore factors through
`A/I` and is a trace.  The head functional is

```text
rho(a)=lim_omega tau(e_lambda a e_lambda).
```

Each term is linear in `a`, since `e_lambda a e_lambda in I` and `theta` is
a trace, so `rho` is linear.  For selfadjoint `a`, orthogonal quasitrace
additivity at `q` gives the exact identity

```text
tau(a)=rho(a)+(tail trace)(a).
```

Thus `tau` is linear.  Since it was arbitrary, every bounded quasitrace on
`A` is a trace.  No sequential cofinal subset of `Lambda` is selected.
