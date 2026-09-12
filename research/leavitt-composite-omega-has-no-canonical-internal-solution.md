---
rg: 2
id: leavitt-composite-omega-has-no-canonical-internal-solution
kind: claim
title: The composite-Omega word has no internal solution among its canonical packet words
artifacts:
  - research/leavitt-composite-omega-has-no-canonical-internal-solution-proof.md
  - research/artifacts/verify-leavitt-composite-omega-cheap-solutions.py
  - research/artifacts/search-leavitt-composite-omega-internal-solutions.py
distinct_from:
  degree-four-kl-source-face-retraction: that constructs a quotient of a weakened packet presentation; this rules out the cheapest full-coefficient-copy retractions obtained by substituting a canonical packet word for the unknown.
  kl-violating-equation-over-leavitt-unit-group: that requires a coefficient kernel in the universal relative quotient; this is only a finite exact internal-solution screen.
---

For

```text
W'=r t e t a t^(-1)c t^2 b t^(-1)d t p t,
b=r^2 a r^(-2),       d=p^2 c p^(-2),
```

none of the `8,201` freely reduced words of length at most four over

```text
{p,p^(-1),q,r,r^(-1),a,e,c,b,d}
```

is a solution of `W'=1` inside the Leavitt elementary group.  This is an
exact Bergman-normal-form calculation in the faithful 20-leaf Leavitt chart.
At radius one, each failure additionally has an explicit moved basis vector
in the faithful infinite-word module.

Thus the strengthened abstract Coxeter retraction is not shadowing a cheap
internal solution of the actual equation.  This does not rule out an
arbitrary internal solution or prove coefficient collapse.
