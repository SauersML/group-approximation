---
rg: 2
id: finite-dyadic-towers-are-neutral-with-one-torus-edge
kind: claim
title: Every finite dyadic depth is scalar-neutral even with one exact unbalanced torus edge
invalidates:
  - sl3-outlier-exclusion-from-finite-dyadic-scalar-gap
distinct_from:
  free-hnn-outlier-has-dyadic-a2-pvm-tower: that extracts one coherent tower at all depths and all arithmetic cosets from a hypothetical enemy; this gives exact finite models at every prescribed depth for the base coset and its denominator translate, including the unbalanced torus/root package.
  finite-lamp-frame-is-matrix-range-neutral: that realizes arbitrary finite free-lamp word windows on a spectator factor but cannot be combined in product form with the unbalanced torus word; this builds the torus coefficients and the two dyadic PVM towers on the same tensor bits, so the denominator covariance is not a spectator.
  unbalanced-torus-forces-cross-gram-on-ambient-face: that excludes the cross-Gram zero packet whenever the lattice data have an exact ambient SL3 reference; this exact finite packet deliberately lacks the remaining SL3 relations and demonstrates why the ambient reference is load-bearing.
---

For every `R>=1` there is a finite-dimensional unitary packet with all of
the following properties.

1. The stable letter `T` has the uniform spectrum of all `2^R`-th roots of
   unity.  Its dyadic spectral projections `q_(r,j)`, `r<=R`, form an exact
   nested trace-flat PVM tower.
2. With `T_1=H^*TH`, the conjugate tower

   ```text
   q_(r,j)^1=H^*q_(r,j)H
   ```

   has exactly the free scalar overlaps, at every pair of retained depths:

   ```text
   tr(q_(r,i) q_(s,j)^1)=2^(-r-s)       (r,s<=R).       (FDT1)
   ```

3. Every displayed lattice coefficient in the two-torus word commutes with
   `T`, the unbalanced torus relator is exact, and

   ```text
   tr(T^*H^*TH)=0.                                     (FDT2)
   ```

4. The intrinsic root package remains nontrivial:

   ```text
   eta_21+eta_32>=sqrt(2).                              (FDT3)
   ```

Thus arbitrarily large nesting depth, all scalar PVM overlaps across one
denominator edge, the first amalgamated-free cross-Gram, and the exact
unbalanced torus/root data coexist in finite matrices.  There is no
dimension-free obstruction depending only on these quantities, no matter
how the bound depends on the retained depth.

This is a finite-depth/all-scalar firewall, not an arithmetic HNN
microstate.  The lattice matrices used below need not satisfy the remaining
`SL_3(Z)` multiplication and Steinberg relations, and the construction does
not realize one common actor on a rank-two coset apartment.  Consequently
the datum left by the all-depth reduction is precise: a proof must propagate
the **same physical nested atoms** through genuinely noncommuting arithmetic
loops (or use equivalent matrix-coordinate information).  Nesting plus the
one-edge cross-Grams and root energies is insufficient.
