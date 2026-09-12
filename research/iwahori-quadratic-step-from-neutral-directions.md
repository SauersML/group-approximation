---
rg: 2
id: iwahori-quadratic-step-from-neutral-directions
kind: route
title: Run the second-order step on a flat neutral direction and count the padding
target: iwahori-uniform-quadratic-repair-step
requires:
  - iwahori-admits-neutral-quadratic-directions
  - second-order-step-beats-a-blocked-linearization
  - word-taylor-remainder-has-a-fourth-moment-bound
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

Let `pi` have defect `e <= eps`.  The first prerequisite supplies the padding
`r <= B e d`, which is clause three of `(QS1)`, and on the padded pair a
`kappa`-flat neutral direction `xi` with `||xi||_(2,d) <= C sqrt e` and the
blocked-component bound of `(NQ1)`, together with a `kappa`-flat linear
correction `eta` of size `O(e)`.

**The norms and admissible map.** Use the map `Psi` and the composed
residual `F` required by `(NQ2)`. The second prerequisite's proof needs
`D^2F` only at `(xi, xi)`, `(xi, eta)`, `(eta, eta)` and `D^3F` only
at `(v,v,v)` along `tv`, where `v=xi+eta`. The explicit chart bounds give

```text
||D^2F(0)[X,Y]||_2 <= C kappa^2 ||X||_2 ||Y||_2    (X,Y in {xi,eta}),
||D^3F(tv)[v,v,v]||_2 <= C ||v||_6^3
    <= C kappa^3 (||xi||_2+||eta||_2)^3 = O(e^(3/2)).
```

The same Taylor calculation as in the second prerequisite therefore
applies. No relative-flatness assertion for `xi+eta` is needed: the
displayed absolute sixth-norm bound suffices, even when the two parameters
cancel. The word Hoelder estimate explains the moment budgets but does
not by itself construct `Psi` or bound derivatives of its composition
with the mismatch map. These are additional hypotheses of `(NQ2)`.

**Output.** The Taylor calculation gives `pi^+=Psi(xi+eta)`, which is
an exact pair of vertex representations by construction, with
`def(pi^+)<=A e^(3/2)`. The movement clause of `(NQ2)` gives distance
`O(sqrt e)` from the padded pair. Padding itself costs exactly
`sqrt(r/(d+r)) <= sqrt(B e)` in the zero-padding metric. Triangle
inequality gives `(QS1)` after enlarging its uniform constant. The
initial bound `def(pi_tilde)<=C e` is essential: arbitrary inexact
blocks of relative size `O(e)` could instead produce defect `O(sqrt e)`.
The constants are uniform by the first prerequisite and hence apply
again to the output pair.

**What this route does not do.**  It does not produce `xi`; the whole content
sits in its first prerequisite, including the admissible chart. The
exact-point vanishing theorem supplies no nonzero projected effect at
compatible pairs; it does not refute the prerequisite near those pairs.
