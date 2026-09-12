---
rg: 2
id: stw81-two-by-two-stationary-colour-grid-proof
kind: route
title: Every two-colouring of the overlapping stationary grid orthogonalizes the fibre colours
target: stw81-stationary-two-colour-interval-patching-forces-af
requires:
  - stw81-z-stable-usc-fields-reduce-to-first-factor-map
artifacts:
  - research/artifacts/stw81-stationary-two-colour-patching-firewall-2026-08-30.md
---

Write

```text
h_l=phi_l(1_(F_l)).
```

For positive `z in F_l`, order zero and positivity give
`0<=phi_l(z)<=||z||h_l`.  Thus `h_0h_1=0` implies all cross products
`phi_0(F_0)phi_1(F_1)` vanish, and the direct sum of the two order-zero maps
is order zero.  It remains to force `h_0h_1=0`.

If either `h_l` is zero there is nothing to prove.  Assume both are nonzero.
For fixed `l`, the two maps `(0,l)` and `(1,l)` cannot have the same global
colour.  Indeed, applying them to the two units gives product

```text
g_0g_1 tensor h_l^2,                                   (SCG1)
```

whose fibre at `t` is nonzero: `g_0(t)g_1(t)>0` and a nonzero positive
element has nonzero square.

There are now only two cases.  If `(0,0)` and `(0,1)` have the same colour,
order zero of that colour gives

```text
g_0^2 tensor h_0h_1=0.
```

Since `(STP1)` implies `g_0(t)>0`, evaluation at `t` gives `h_0h_1=0`.
Otherwise `(0,0)` and `(0,1)` have different colours.  By `(SCG1)`, each
fixed fibre label must switch colour between base patches.  Hence `(0,0)`
and `(1,1)` have the same colour, and their product gives

```text
g_0g_1 tensor h_0h_1=0.
```

Evaluation at `t` again gives `h_0h_1=0`.  This proves `(STP3)` for every
possible two-colouring.

Now suppose that for every finite subset and tolerance in `D` one starts
with a two-colour nuclear-dimension approximation

```text
D --psi--> F_0 direct_sum F_1 --phi_0+phi_1--> D
```

and its stationary localization `(STP2)` admits the asserted two-colouring
over an overlap.  The preceding argument makes the whole return map c.p.c.
order zero: orthogonality gives order zero, and the sum of the orthogonal
positive support elements has norm at most one, giving contractivity.
These are nuclear-dimension-zero approximations of `D`.
Nuclear dimension zero is equivalent to being AF, proving the firewall.

For a general upper-semicontinuous field the local lifts at different
anchors need not be stationary copies, so the argument does not compare
their support elements.  This is exactly why the theorem is a no-go for the
natural fixed-frame construction rather than a negative solution of the
first-factor problem.
