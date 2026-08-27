---
rg: 2
id: junge-riesz-bmo-does-not-close-code-newton
kind: claim
title: Published noncommutative Riesz and John--Nirenberg bounds do not yet close code Newton
distinct_from:
  code-riesz-inverse-is-averaged-first-split: that supplies the exact permutation-martingale identity; this audits the exact hypotheses and endpoint scope of the proposed literature imports.
  jnvwy-pasting-does-not-close-ldpc-synchronization: that audits quantum tensor-code agreement; this audits harmonic-analysis control of the exact code Riesz inverse.
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that isolates the analytic operator; this checks two proposed literature imports against it.
---

The Hamming length on the finite code-character group,

```text
psi(z)=wt(z),                                             (JRB1)
```

is conditionally negative: it is the squared norm of the coordinate cocycle
with sign action.  Therefore the dimension-free `L_p`, `1<p<infinity`, Riesz
transform estimates of Junge--Mei--Parcet apply, including matrix
amplifications and standard Fourier-to-Schur transference at an exact
character decomposition.

This is useful but does not prove `(CRM3)` or
`balanced-overlay-diffuse-square-function-newton`.

* The JMP Riesz symbol is `b(z)/sqrt(psi(z))`.  The coordinate inverse has
  symbol `b_i(z)/psi(z)`, so it also contains an inverse-square-root
  Laplacian.  The code gap `psi(z)>=delta L` controls this symbol pointwise,
  but pointwise Fourier bounds do not by themselves give a cb multiplier
  bound.  `code-laplacian-has-uniform-cp-green-approximants` gives fixed-
  accuracy CP approximants, not an endpoint inverse theorem.
* JMP Theorems A1--A2 are stated for `1<p<infinity`.  The paper explicitly
  says that its approach does **not** give `L_infinity -> BMO` estimates.
  Thus it cannot be cited for the endpoint row/column estimate required by
  Newton.
* `code-riesz-inverse-is-averaged-first-split` puts the exact coefficient
  average into permutation martingale filtrations.  Junge--Musat Theorem 1.1
  gives `BMO_p<=Cp BMO` for an element of one fixed martingale filtration,
  and Theorem 1.2 gives, for one BMO element, a one-sided projection `f` with
  `||(x-x_0)f||_op<=t` and exponentially small complement.  It does not prove
  the missing vector-valued bound for the layer-dependent array
  `b_(i,pi(k))`, nor produce one base-algebra projection common to all
  permutations, output coordinates, rows and columns.  Averaging the
  filtration-dependent projections yields a positive contraction, not a
  common reducing projection.
  Quantitatively, the standard fixed-permutation transform estimate controls
  the unnormalized square function
  `||(sum_j b_(i,j)^*b_(i,j))^(1/2)||_op`; relative to the normalized
  coordinate row norm this loses `sqrt(L)`.  Averaging those BMO norms by
  convexity cannot recover the missing `1/sqrt(L)` gain.  Encoding all
  outputs as one row instead puts the Cuculescu projection in
  `M_L tensor M_d`; it need not have product form `I_L tensor q`.  A usable
  endpoint therefore needs an exponential tail estimate for the physical
  square function `L^(-1)sum_i X_i^*X_i`, or a product-cut theorem.
* Both harmonic-analysis descriptions require the exact code-character
  decomposition and its conditional expectations.  The diffuse Newton gate
  starts before exact parity/shared commutation has been obtained.  Importing
  those expectations there assumes the desired basin.

Finite-`p` Riesz estimates may still support a new truncation proof: their
constants depend only on `p`, and one could choose growing `p` to pay a
summable exceptional trace.  To make that rigorous one must first prove the
vector-valued first-split martingale estimate and construct compatible
approximately reducing cuts without exact characters.  Neither cited paper
contains that promotion.
