# Affine--Leavitt--Steinberg normalized-HS decoder audit

**Integrated:** 2026-08-21  
**Status:** rigorous reduction dossier; no nonhyperlinear group is claimed.

The supplied full investigation was checked against Cairn and integrated by
reference rather than copied into duplicate claims.  The exact coefficient
and group-theoretic pieces were already present:

- `affine-active-corner-has-faithful-binary-leavitt-envelope`;
- `relative-leavitt-active-subspaces-expand-by-two`;
- `affine-leavitt-steinberg-mark-is-fd-invisible`;
- `approximate-relative-leavitt-cell-kills-active-trace`;
- `fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity`;
- `steinberg-root-shear-plancherel-covariance`;
- `rectangular-escape` and `tensor-independent-child-carrier-gap`.

The dossier correctly does **not** close
`affine-leavitt-steinberg-hs-coefficient-decoder` or
`affine-leavitt-boundary-shear-payment`.  The exact rectangular model remains
decisive: paired label dimension may double while Weyl multiplicity shrinks,
with unchanged ambient matrix dimension.  Deterministic equivariance,
finite-depth Fourier functoriality, and canonical Plancherel marginals alone
therefore cannot prove normalized marked-mass loss.

## New theorem promoted

`bistochastic-diagonal-return-forces-aligned-permutation` is the new complete
sublemma from the dossier.  For square bistochastic kernels `K,L`, a
near-maximal normalized cyclic overlap `Tr(LK)/N` forces `K` within `2 eta`
of a permutation and `L` within `5 eta` of its inverse.  The proof uses only
Frobenius concentration and Birkhoff--von Neumann, so the constants are
independent of the alphabet size.

This materially narrows the affine-Leavitt frontier.  Once source and target
are proved to occupy the same source-sized paired reservoir, the diagonal
return laws automatically supply the deterministic transports needed by the
existing robust `1/36` paired floor.  The sole remaining local conversion is
therefore:

```text
actual rank-five canonical microstate
  -> same paired multiplicity reservoir, or paid boundary leakage.
```

Equivalently, prove at each fixed depth that reciprocal label expansion and
multiplicity contraction cannot complete a closed return cycle on the same
positive-density carrier without a normalized-HS payment.  This is exactly
the open content of `affine-leavitt-boundary-shear-payment`; constants may
depend arbitrarily on the fixed depth.

## Falsification boundary retained

A proposed completion must still defeat rectangular enlargement, avoid
turning HS-small errors into rank-small errors, retain the unclosed
coefficient boundary, use a common coupling rather than four unrelated
marginals, and invoke a genuinely matrix-coordinate feature.  Any argument
valid in every finite tracial von Neumann algebra would also hit the left
regular representation and cannot be the missing decoder.
