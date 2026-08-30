---
rg: 2
id: stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap
kind: claim
title: A zero-dimensional nuclear Bauer completion can have a nonzero but bounded-trace-free fibre gap
distinct_from:
  stw22-tracefree-fibre-gap-ideals-force-trace-continuity: that theorem gives an abstract sufficient condition on every fibre gap; the present theorem computes a nonzero gap in an actual uniform tracial completion of a separable nuclear algebra and proves the condition directly.
  stw22-norm-fibre-gap-is-the-trace-obstruction: that theorem isolates the abstract norm-fibre obstruction; the present theorem shows concretely that equality of the norm and 2-norm fibre ideals is already too strong in the easiest infinite Bauer example.
artifacts:
  - research/artifacts/stw22-convergent-sequence-gap-audit-2026-08-30.md
---

Let

```text
X={infinity,1,2,...}
```

be the one-point compactification of the natural numbers, let `U` be an
infinite-dimensional UHF algebra with its unique trace, and put
`A=C(X) tensor U`.  If `R=pi_tau(U)''`, then the uniform tracial completion
of `A` is canonically

```text
M={ (a_infinity,a_1,a_2,...):
      a_n in R, sup_n ||a_n||<infinity,
      ||a_n-a_infinity||_2 -> 0 }.
```

At the point `infinity`, its 2-norm fibre ideal and central norm-fibre ideal
are

```text
K_infinity={a in M:a_infinity=0},
J_infinity={a in K_infinity:||a_n|| -> 0}.
```

Consequently

```text
K_infinity/J_infinity
  ~= { (a_n) in product_n R: ||a_n||_2 -> 0 }
       / { (a_n): ||a_n|| -> 0 }.                         (CSG)
```

The gap `(CSG)` is nonzero and not sigma-unital, but it has no nonzero
bounded positive trace.
Thus `J_x=K_x` can fail even for a separable nuclear algebra with
zero-dimensional compact extremal boundary, whereas the intrinsic
trace-free-gap condition still holds.

This example also fences the stability shortcut.  The gap is already
non-sigma-unital, so the usual sigma-unital stability criteria do not apply.
The argument proves bounded-trace-freeness directly and does not decide
whether `(CSG)` is stable in the non-sigma-unital sense; stability is not
needed for Problem XXII and should not be substituted for the exact trace
condition without an independent stabilization argument.
