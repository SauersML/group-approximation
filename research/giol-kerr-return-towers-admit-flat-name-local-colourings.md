---
rg: 2
id: giol-kerr-return-towers-admit-flat-name-local-colourings
kind: claim
title: Giol-Kerr return towers admit flat name-local colourings
distinct_from:
  stw99-problem-xxxiv-dynamical-characterisation: that asks whether absolute Z-stability forces the Cartan-relative small-boundary properties; the projections here are deliberately off-diagonal and seek only absolute uniform Gamma.
  stw99-problem-xx-villadsen-algebras-uniform-gamma: that AH stable-rank-one family is positive by Vaccaro; Giol-Kerr orbit-breaking stages are recursive subhomogeneous and the needed continuous return-tower selection is not covered by the AH theorem.
  stw99-problem-xxxv-giol-kerr-tracial-completion: that compares completed tracial geometries with Villadsen algebras; this is a direct finite-stage criterion requiring no completion identification.
---

Let `h:X->X` be one of the free minimal Giol--Kerr systems, let
`A=C(X) rtimes_h Z`, let `u` be the implementing unitary, and write

`||a||_(2,u)=sup{tau_mu(a* a)^(1/2): mu in M_h(X)}`.

For every integer `n>=2`, finite self-adjoint `F subset C(X)`, and
`epsilon>0`, there is a sufficiently deep first-return recursive
subhomogeneous stage, with tower charts `(Y_l,H_l)`, and continuous
positive contractions

`Q_(l,1),...,Q_(l,n):Y_l -> M_(H_l)`

having the following properties.

1. The `Q_(l,r)` respect all recursive-subhomogeneous boundary maps and
therefore assemble to elements `q_1,...,q_n` of the orbit-breaking
stage, hence of `A`.
2. In normalized Hilbert--Schmidt norm, uniformly in `l` and `y`, they
are an `epsilon`-projection partition:
   `Q_(l,r)^2 approx Q_(l,r)`, `Q_(l,r)Q_(l,s) approx 0` for `r!=s`, and
   `sum_r Q_(l,r) approx 1`.
3. They are flat on the tower diagonal: if `d_(l,r,j)(y)` is the `j`th
   diagonal entry of `Q_(l,r)(y)`, then
   `(H_l^(-1) sum_j |d_(l,r,j)(y)-1/n|^2)^(1/2)<epsilon`.
4. They are name-local. For
   `D_(l,f)(y)=diag(f(y),f(hy),...,f(h^(H_l-1)y))`, one has
   `||[Q_(l,r)(y),D_(l,f)(y)]||_(2,H_l)<epsilon`
   for every `f in F`.
5. The return-successor and tower-seam defects are uniformly tracially
small: after assembly,
   `||[q_r,u]||_(2,u)<epsilon`.

Here `||.||_(2,H)` is normalized Hilbert--Schmidt norm. Heights not
divisible by `n` may discard fewer than `n` levels; the resulting
`O(n/min H_l)` errors are included in the displayed tolerances.

## Attempts

**OPEN.** This is the smallest direct finite-stage selection statement
currently missing for the Giol--Kerr examples.

- A fixed Fourier `n`-colouring in each matrix tower gives the partition
  and flat-diagonal clauses, but
  `||[Q,D_f]||_(2,H)^2 = H^(-1) sum_(i,j)|Q_(i,j)|^2 |f(h^i y)-f(h^j y)|^2`;
  independently varying Giol--Kerr names keep this bounded away from zero.
- Pointwise clustering the indices by their finite `F`-names and
  Fourier-splitting inside each cluster makes the same formula small
  while retaining flat diagonal up to `o(H)`. The cluster pairing
  changes discontinuously at collision strata and presently cannot be
  made compatible simultaneously with the recursive boundary maps and
  the return successor.
- Stable rank one of the crossed product does not manufacture this
  continuous selection. Vaccaro's 2026 theorem obtains the analogous
  selection for AH algebras through tracial local homogeneity; that
  hypothesis has not been verified for these recursive subhomogeneous
  return stages.
- Positive mean dimension rules out diagonal/Cartan-relative uniform
  Gamma (the small boundary property), but it does not rule out the
  off-diagonal tower projections above. Thus relative-Gamma failure is
  neither a proof nor a refutation of this claim.
