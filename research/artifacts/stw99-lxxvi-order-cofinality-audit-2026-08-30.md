# STW Problem LXXVI: first-factor order-cofinality audit (2026-08-30)

## What is new

The existing LXXVI graph identifies the ideal lattice, K-theory, and
quasitraces of `A` and `A tensor Z`, and separately proves order reflection
when the left source class is soft.  It did not record a comparison-theoretic
density property of the actual first-factor image.

The new theorem works for every unital tensor factor `B`: each way-below
window in `Cu(A tensor_min B)` is dominated by one class of the form
`[d tensor 1_B]`, and a countable sum gives one such dominator for an
arbitrary target class.

## Algebraic-tensor audit

For a finite tensor `z=sum alpha_j tensor b_j`, write `z=RC`, where `R` is
the row of first-factor coefficients and `C` is the column of second-factor
coefficients.  Then

```text
zz* <= ||C||^2 RR*
    = ||C||^2 (sum_j alpha_j alpha_j*) tensor 1_B.
```

This remains valid for nonunital `A`: the entries `1 tensor b_j` live in the
multiplier algebra and their products with the `alpha_j tensor 1` entries
lie in the stabilized minimal tensor product.  The equality of the Cuntz
classes of `z*z` and `zz*`, plus the usual perturbation comparison
`(a-epsilon)_+` below `z*z`, gives the local result.  No slice-map theorem or
tensor exactness is hidden in the argument.

## Boundary sharpened by the diagonal theorem

This is upper or outer cofinality, not inner cofinality.  The dominating
first-factor class can extend far outside the hereditary support of the
target class.  The distinction is essential: the corrected theorem
`stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product` shows that
order reflection plus genuine inner brackets diagonalizes to a Cu-isomorphism.
Thus the new automatic result removes lack of upper dominators as an LXXVI
obstruction but does not solve injectivity, surjectivity, or inner rank
realization.
