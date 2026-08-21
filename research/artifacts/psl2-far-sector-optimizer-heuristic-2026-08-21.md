# PSL2 far-sector optimizer: heuristic protocol and smoke data

Date: 2026-08-21.

This artifact records the bounded experiment in
`experiments/psl2_far_sector_probe.py`. It is hypothesis-generating only; it
is not a numerical lower-bound certificate and is not evidence for flexible
Hilbert--Schmidt stability.

## What is controlled exactly

The variables are four unitary matrices `(x,y,x',y')`. Spectral conjugation
keeps

```text
x^2=x'^2=1,                 y^3=y'^3=1
```

exact throughout optimization, with approximately balanced multiplicities of
the order-two and order-three eigenvalues. The measured defect is the maximum
of the two corrected Iwahori amalgam residuals

```text
xy-(x'y')^2,
xy^2xyx-x'y'x'y'^2x'.
```

The repulsion diagnostic is

```text
min { ||(xy)^m-I||_2 : m odd, 1<=m<=M },
```

where `M` is a user-chosen dimension-dependent cutoff. The loss rewards this
quantity while minimizing the two amalgam residuals.

## Smoke data

The MSI smoke run used `d=6`, one restart, `120` Adam steps and two repulsion
weights. The retained summary is
`experiments/psl2-far-sector-probe-smoke.json`:

| repulsion `mu` | best defect | tested odd-power farness |
|---:|---:|---:|
| 0 | 0.5199918743 | 1.3894460134 |
| 1 | 0.5739660814 | 1.3552177645 |

The repulsion did not produce a lower-defect far point in this tiny run. This
is only a development signal that the objective and exact-torsion
parameterization execute coherently.

## Why this proves nothing

- The odd-power diagnostic is not distance to the compatible or congruence
  representation locus. Exact direct sums may have arbitrarily large odd
  order, beyond the cutoff.
- The optimizer is nonconvex, used one random restart, and provides neither a
  global optimum nor a certified lower bound.
- Dimension six and 120 steps cannot probe an asymptotic stability question.
- The loss checks the two chosen presentation residuals, not character
  convergence to the regular trace and not distance after flexible padding.
- A positive residual can be optimizer failure; a near-zero residual would
  still require an independent proof of farness from every exact compatible
  representation.

Accordingly the experiment suggests only a next iteration strategy: validate
candidate adversarial seeds and objective scaling cheaply before investing in
larger MSI runs. No Cairn claim depends on the numerical values.
