---
rg: 2
id: irrep-window-hs-gap-no-go-proof
kind: route
title: Rank-one surgery is invisible to fixed words but kills the irreducible-block gap
target: irrep-window-does-not-force-hs-gap
requires:
  - rank-one-lift-perturbation-gap-no-go
  - finite-window-hs-tests-ignore-low-rank-generator-surgery
---

Use the explicit construction in the proof of
`rank-one-lift-perturbation-gap-no-go`.  There `Gamma=SL_3(Z)` and the genuine
irreducible augmentation representations `rho_n` have dimensions tending to
infinity.  Each generator is first changed on a subspace of dimension at most
two so as to almost fix a rank-one projection `q_n`, and is then perturbed in
operator norm by `d_n^(-2)` to a tuple `V_n` with joint commutant exactly
`C`.  Thus the generator algebra is irreducible and has a single full-trace
block.

The first surgery has rank at most two and the generic second perturbation has
normalized HS norm at most its operator norm.  Therefore every generator of
`V_n` is `O(d_n^(-1/2))` from the corresponding generator of the genuine
representation `rho_n`.  By
`finite-window-hs-tests-ignore-low-rank-generator-surgery`, every fixed word
has the same asymptotic value on `V_n` as on `rho_n`.  In particular every
fixed relation word of `Gamma` has defect tending to zero.  The same
word-telescoping statement applies to any fixed finite multiplication-table
window.

On the other hand the construction supplies

```text
x_n=q_n-d_n^(-1)1,
||x_n||_2^2=d_n^(-1)(1-d_n^(-1)),
max_s ||[V_(s,n),x_n]||_2 <= 2 d_n^(-2).
```

After normalizing `x_n`, its adjoint Rayleigh quotient is at most

```text
4 |S| d_n^(-4) / (d_n^(-1)(1-d_n^(-1))) -> 0.
```

So the only irreducible block has vanishing adjoint gap despite vanishing
defect on every fixed relation window.  This proves all three assertions and
rules out the zero-boundary irreducible-selection strategy.
