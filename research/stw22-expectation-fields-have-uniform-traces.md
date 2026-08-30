---
rg: 2
id: stw22-expectation-fields-have-uniform-traces
kind: claim
title: Zero-dimensional continuous-expectation factor fields have only uniform traces
distinct_from:
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem uses fixed target corners in one constant factor; the present theorem permits genuinely moving finite-factor subalgebras and constructs weighted orthogonal copies inside each moving fibre.
  stw22-dense-factor-fields-have-uniform-traces: that theorem uses finite Cantor--Bendixson descent for a concrete nuclear class; the present theorem removes every height restriction once the fibre expectations vary continuously in the common ambient factor.
artifacts:
  - research/artifacts/stw22-variable-factor-selection-audit-2026-08-30.md
---

Let `K` be compact, metrizable, and zero-dimensional, let `(R,tau)` be a
finite factor, and for every `x in K` let `N_x subset R` be a unital finite
factor.  Write `E_x:R -> N_x` for the trace-preserving conditional
expectation and assume

```text
x |-> E_x(z) is ||.||_2-continuous for every z in R.    (CEF)
```

Define

```text
M={a:K -> R: sup_x ||a(x)||<infinity,
                 a(x) in N_x,
                 x |-> a(x) is ||.||_2-continuous}.
```

Then `M` is a factorial tracially complete `C(K)`-algebra and every
tracial state on `M` is uniquely

```text
a |-> integral_K tau(a(x)) dmu(x)
```

for a probability measure `mu` on `K`.  In particular every trace on `M`
is continuous for the uniform `2`-norm.

Consequently STW Problem XXII has a positive answer for every C*-algebra
whose uniform tracial completion admits this continuous-expectation
presentation.  This includes the asymptotically dense changing-factor
fields of `stw22-dense-factor-fields-have-uniform-traces` and any of their
closed zero-dimensional subfields.

No Cantor--Bendixson height assumption occurs.  Thus compact metrizable
scattered bases of arbitrary countable successor or limit height are
covered whenever `(CEF)` holds.  The theorem does not assert that an
arbitrary factorial tracial bundle embeds into one common finite factor
with continuous fibre expectations; that common-ambient condition is the
remaining structural boundary.
