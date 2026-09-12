---
rg: 2
id: dilution-obstructs-flat-quadratic-iwahori-repair
kind: claim
title: Dilute Iwahori errors defeat a uniform sixth-moment-flat quadratic repair step
distinct_from:
  normalized-hs-taylor-remainder-is-not-dimension-free: that refutes an ambient second-derivative bound using one spiked tangent; this gives exact vertex inputs for which every superlinear repair must make concentrated movement, so forbidding spikes in the chosen chart does not solve the global problem.
  commuting-repair-forces-half-dimension-rank: that forces high-rank changes for a small-defect clock-shift pair; this forces fixed operator-norm movement on a dilute incompatible block and excludes bounded moment ratios at the specified rates.
  modular-vertex-charts-have-uniform-schatten-control: that proves admissibility and derivative bounds for explicit coordinates; this proves the universal flat quadratic-direction proposal cannot succeed in those coordinates.
artifacts:
  - research/artifacts/iwahori-dilution-moment-obstruction-2026-09-08.md
---

Let `chi:SL_2(Z)->U(1)` have `chi(s)=-1`, `chi(b)=1` for
`SL_2(Z)=<s,b | s^2=b^3, s^4=1>`. The exact modular pair
`pi_1=1_n`, `pi_2=chi (+) 1_(n-1)` has Iwahori defect
`e_n=2/sqrt(n)` and agrees exactly on the common central involution.

Pad by arbitrary exact vertex pairs to dimensions `N_n<=C_0 n`.
Every output pair `V` with `def(V)=O(e_n^(1+beta))`, `beta>0`, has
maximum generator operator-norm movement at least `(2-o(1))/6` from
that padded input. If its maximum normalized-HS movement is
`O(e_n^alpha)`, the ratio of its maximum Schatten-p movement to its
maximum HS movement is at least `c n^(alpha/2-1/p)`.

Consequently bounded moment ratios are impossible when `alpha p>2`.
In particular, in the explicit modular charts, there are no uniform
constants `A,B,C,kappa` providing for every input a padding
`r<=B e_n n` and parameters `xi,eta` with

```text
||xi||_2<=C sqrt(e_n),       ||eta||_2<=C e_n,
||xi||_6<=kappa||xi||_2,     ||eta||_6<=kappa||eta||_2,
def(Psi(xi+eta))<=A e_n^(3/2).
```

This refutes that natural-chart specialization, not the arbitrary-map
formulation of `iwahori-admits-neutral-quadratic-directions`. The same
inputs admit exact same-dimensional repairs of HS cost `e_n` by
replacing `chi` with the trivial character. No failure of flexible
stability or nonhyperlinear group follows.
