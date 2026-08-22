---
rg: 2
id: six-shell-hecke-gap-is-blind-to-cross-chart-gram-energy
kind: claim
title: The full six-shell Hecke gap is blind to cross-chart Gram energy
distinct_from:
  two-equivariant-shell-pvms-have-independent-coordinate-escape: that gives the minimal two-chart countermodel and identifies one off-diagonal orbital; this realizes all six Weyl charts simultaneously, computes the full star-authentication deficit, and shows that property-T or Hecke expansion cannot improve it.
  six-parahoric-finite-fiber-folds-remain-amenable: that uses coweight Folner boxes and arbitrary finite transition fibers to defeat local denominator stencils; this is a fixed finite exact lattice calibration showing that even a nonamenable shell action has zero coercivity on cross-chart Gram mismatch.
  five-parahoric-overlap-saturations-give-global-shell-pvm: that proves five cross-trace saturations are sufficient to identify all charts; this proves those five scalars are independent input and cannot be deduced from the six individual Hecke Dirichlet forms.
---

Let

```text
C=SL_3(Z),       D=C cap hCh^(-1),       Omega=C/D,
|Omega|=42.                                             (SHG1)
```

Use the canonical bijections from the six Weyl parahoric charts to `Omega`.
On

```text
H=l^2(Omega^6)                                         (SHG2)
```

let `C` act diagonally.  For each chart `w in S_3` and `i in Omega`, let
`P_(w,i)` be multiplication by the indicator that the `w`-coordinate is
`i`.  Then every chart is a complete PVM and is exactly covariant under the
same actor representation:

```text
rho(g)P_(w,i)rho(g)^*=P_(w,gi).                         (SHG3)
```

Consequently every property-`(T)` or finite Hecke Dirichlet form internal
to any or all of the six charts is exactly zero.  All integral root,
Steinberg, mixed-root, and Weyl relations in `C` also hold exactly.

Fix one root chart `w_0`.  For every other chart `w`, corresponding atoms
are independent coordinates, so

```text
tr(P_(w,i))=1/42,
tr(P_(w,i)P_(w_0,i))=1/42^2,                            (SHG4)
```

and hence

```text
Delta_w=(1/2)sum_i||P_(w,i)-P_(w_0,i)||_2^2=41/42.
                                                               (SHG5)
```

The complete five-edge star deficit is therefore

```text
sum_(w!=w_0) Delta_w=205/42,                            (SHG6)
```

while the sum of all six shell Hecke energies is zero.  Tensoring `(SHG2)`
with regular representations of deeper and deeper congruence quotients of
`C` makes every fixed nonidentity lattice trace vanish without changing
`(SHG3)--(SHG6)`.  Thus the calibration lies in the canonical lattice
character sector.

## Spectral reason

On two chart coordinates the diagonal `C`-action preserves every orbital
in `Omega times Omega`.  The diagonal matching is only one such orbital.
The shell Markov operator has eigenvalue one on the indicator of every
orbital, so its Poincare inequality controls variation *inside* each
orbital and has no coercivity on the total mass assigned to distinct
orbitals.  Taking six coordinates does not remove this kernel; it merely
creates the corresponding multi-orbital algebra.

Therefore no inequality of the form

```text
sum_(w!=w_0) Delta_w
 <=K (sum of six lattice/Hecke covariance energies)     (SHG7)
```

can hold, for any dimension-independent `K` (indeed, for any `K`).  The
full coset PVM does not turn property `(T)` into support authentication.

The missing term is exactly a denominator incidence selecting the diagonal
orbital.  `raw-denominator-incidence-kills-off-diagonal-shell-orbit` gives
the square-function identity

```text
sum_i(P_i-Q_i)^2=2(1-R_diag),                           (SHG8)
```

when that raw incidence is present.  Hence the remaining problem is not a
stronger Hecke spectral gap: it is to lift `(SHG8)` from the raw lamp
conjugates to the decoded joint atoms with error charged to first exits.

This finite calibration deliberately does not extend the six independent
coordinates to the denominator generator of `SL_3(Z[1/2])`.  Exact such an
extension is forbidden by co-density.  It proves precisely that the
denominator-incidence row is indispensable; it is not a countermodel to the
full arithmetic transfer statement.

