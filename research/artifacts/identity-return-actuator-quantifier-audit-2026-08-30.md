# Identity-return actuator quantifier audit (2026-08-30)

## Calculation

The actuator is stated for an arbitrary ambient word `r`.  Put `r=1` and
take any `L>=1`.  After packet exactification,

```text
||q 1 q||_2^2 = ||q||_2^2 = tr(q) -> alpha,
```

whereas `(ACA1)` requires a limit at most `alpha rho^(2L)<alpha`.

Hence any output satisfying the estimate at `r=1` has no canonical-profile
matrix microstates.

## Interpretation

This is not an unconditional refutation.  The estimate is universal over
canonical-profile microstates and can be vacuous when none exist; clause 3
supplies an exact perfect representation, not a canonical-profile finite
matrix model.  Under strict logic the identity specialization therefore makes
the constructor already root-strength.

The actual pairwise-packing consumer uses fresh reduced relative words
`r_ij=v_i^*v_j` with `i!=j`.  A corrected actuator should quantify only
over that noncollapsed input class and state the needed ambient/free-product
embedding condition explicitly.
