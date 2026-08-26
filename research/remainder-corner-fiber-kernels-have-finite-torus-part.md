---
rg: 2
id: remainder-corner-fiber-kernels-have-finite-torus-part
kind: claim
title: Compression stationarity transports the top-dimensional torus part of a fiber kernel variety exactly, finite-orbit subvarieties of the torus are points or the torus, so remainder-corner fiber kernels meet the torus in finitely many points
distinct_from:
  remainder-corner-fiber-kernels-are-monomial-free: that shows the random kernel ideal contains no monomial, i.e. its variety is not inside the coordinate hyperplanes; this shows the variety meets the torus in a finite set, so the ideal is a boundary-deep multiple of a cofinite ideal, and it introduces the stationarity-with-potential method on the law of the random ideal.
  kt-compression-fixed-tracial-states-are-atomic-or-regular: that is the open classification; this is the strongest proved constraint so far on any counterexample: its fiber kernels are almost surely of the form `(x_1...x_d)^M . S` with `S` cofinite, and the law of the saturations is exactly transported by the substitutions with colength preserved.
---

Setting of `remainder-corner-fiber-kernels-are-monomial-free`: `Gamma =
EL_r(F_q[x_1..x_d])`, `d >= 3`, `r > sr`, a compression-fixed character `chi`
on the remainder corner with extremal decomposition `mu`, and the random
nonzero, monomial-free kernel ideal `J_omega`.  Write `V(J)` for the variety
in `bar F_q^d`, `V^0(J) = V(J) cap (bar F_q^*)^d` for its torus part, and
`Phi_A(p) = (p^(A e_1), ..., p^(A e_d))` for the monomial map of
`A in SL_d(Z)`, which is an automorphism of the torus.

**Theorem.**
1. (Stationarity with potentials.)  For every compression `phi_A`, the
   transport of `remainder-corner-monomial-free-proof` couples `J_omega` with
   the kernel ideal `J_(omega')` of a random component of
   `chi_omega o phi_A`, with `J_(omega') supseteq phi_A^(-1)(J_omega)` and
   `J_(omega') ~ mu`.  Hence any integer-valued function `h` on ideals that is
   non-increasing along `J -> J' supseteq phi_A^(-1)(J)` is almost surely
   constant along the coupling.
2. (Exact transport of the torus part.)  Let `T(J)` be the union of the
   top-dimensional irreducible components of `V^0(J)`.  Almost surely
   `T(J_(omega')) = Phi_A(T(J_omega))`, so the law of `T(J_omega)` is
   invariant under every `Phi_A`, `A` a transvection, hence under the
   monomial action of `SL_d(Z)`, and almost every value has a finite
   `SL_d(Z)`-orbit.
3. (Finite-orbit subvarieties.)  For `d >= 2`, an irreducible closed
   subvariety `V` of the torus `(bar F_q^*)^d` whose stabilizer in
   `SL_d(Z)` (monomial action) has finite index is either a point or the
   whole torus.
4. (Conclusion.)  Almost surely `V(J_omega) cap (bar F_q^*)^d` is finite.
   Equivalently the saturation `S_omega = J_omega : (x_1...x_d)^infty` is a
   cofinite ideal of `R_+`, and `J_omega supseteq (x_1...x_d)^(M_omega) S_omega`
   for some `M_omega`.  Moreover the law of `S_omega` is exactly transported:
   almost surely `S_(omega') = phi_A^(-1)(S_omega)` with
   `colength(S_(omega')) = colength(S_omega)`, so the substitution subring
   `phi_A(R_+) = F_q[x^(A e_1), ..., x^(A e_d)]` surjects onto the finite ring
   `R_+/S_omega` for every transvection `A`.

**What this says about a counterexample.**  Its fiber representations are
trivial on `E(R_+, (x_1...x_d)^M S)` with `S` cofinite: the kernels are
"boundary-deep" relative elementary groups, everything happening in the
coordinate hyperplanes of the variety.  On root subgroups, the spectral
measure of each component is therefore Haar on every coordinate `x^v`
with some `v_i < M_omega`, in particular on all coordinates lying on a
coordinate hyperplane, independently of the deep interior coordinates.
The remaining freedom of the remainder corner is entirely in the deep
interior cone, and the next fence is to show that the compression
transport of the interior data (which the substitution maps stretch into
the interior) is incompatible with the persistent non-regularity of
`remainder-corner-root-character-is-persistently-nonregular`.
