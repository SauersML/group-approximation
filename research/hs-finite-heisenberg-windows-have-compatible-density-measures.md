---
rg: 2
id: hs-finite-heisenberg-windows-have-compatible-density-measures
kind: claim
title: Finite additive and Heisenberg windows have exact compatible HS multiplicity-density measures
distinct_from:
  finite-root-heisenberg-multiplicity-germs: that produces integer rank germs for an operator-norm matrix-corona representation; this produces real normalized multiplicity densities in a tracial matrix ultraproduct.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: that must assemble all finite-window densities and four coefficient maps on one common positive-density part of the prescribed root carrier; this proves only the exact finite-window inverse system.
---

Let `u_n:E_r(R)->U(d_n)` be a normalized-Hilbert--Schmidt asymptotic
representation.  Fix finite additive subgroups `A,B,C` of `R` with `AB<=C`
and three distinct root positions.  In the tracial matrix ultraproduct the
root words generate an exact representation of the finite Heisenberg group

```text
H(A,B,C)=<x_ij(A),x_jk(B),x_ik(C)>.
```

For every `pi in Irr(H(A,B,C))`, let `e_pi` be its primitive central
projection and define the normalized multiplicity density

```text
nu_(A,B,C)(pi)=tau(e_pi)/dim(pi).                       (HHD1)
```

These nonnegative densities satisfy

```text
sum_pi dim(pi) nu_(A,B,C)(pi)=1.                       (HHD2)
```

For every inclusion of finite windows, the density vector restricts by the
ordinary integral branching matrix.  The same statement for one additive
root gives the exact compatible Fourier-character density measures.

Equivalently, after flexible finite-group HS exactification at the
coordinates, the normalized irreducible multiplicities have the ultralimit
`(HHD1)` and obey all finite restriction identities up to `o(1)`.  Thus the
operator-norm rank-germ theorem is not needed in the HS lane.

If a characteristic-two root `v` survives with
`lim_omega||u_n(v)-1||_2>0`, its spectral projection `(1-u(v))/2` has
positive tracial-ultraproduct trace.  Hence at least one finite-window
multiplicity density meeting that root sector is positive.  This does not
yet prevent that mass from moving among types as the window grows.
