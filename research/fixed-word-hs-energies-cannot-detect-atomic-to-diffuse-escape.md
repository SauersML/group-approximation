---
rg: 2
id: fixed-word-hs-energies-cannot-detect-atomic-to-diffuse-escape
kind: claim
title: Fixed word Hilbert--Schmidt energies cannot detect atomic spectra converging to Haar
distinct_from:
  summable-abelian-checksum-misses-infinite-characters: that constructs two-character swaps defeating a summable diagonal covariance library; this is the general tracial-moment continuity fence for arbitrary fixed mixed word polynomials and spherical conjugation averages.
  affine-leavitt-tracial-square-function-firewall: that substitutes the regular representation into a proposed universal finite-tracial derivation; this identifies exactly which matrix-microstate statistics disappear under atomic-to-diffuse ultralimit even before a terminal inequality is proposed.
  finite-spherical-moments-do-not-fold-regular-double: that proves finite atomic quadrature for one arithmetic Hecke spectrum; this applies to any already-given canonical matrix microstate sequence and any fixed word-polynomial energy.
---

**ESTABLISHED CONTINUITY FENCE.**  Let `Gamma=<S|R>` be finitely generated
and let `U^(n)=(U_s^(n))_(s in S)` be matrix tuples converging in tracial
`*`-moments to a tuple `U=(U_s)` in a finite tracial von Neumann algebra.
For every fixed finite family of matrix-valued noncommutative
`*`-polynomials `p_1,...,p_q`, all quantities

```text
tr_n(p_i(U^(n))),
<p_i(U^(n)),p_j(U^(n))>_2,
||p_i(U^(n))||_2^2,                                    (FWE1)
```

converge to the corresponding quantities at `U`.  The same holds for every
fixed finitely supported conjugation average

```text
A_(mu,U)(X)=sum_g mu(g) U_g X U_g^*                   (FWE2)
```

when `X` is a fixed word polynomial, and for finite Gram/SOS expressions
built from such vectors.

Consequently, suppose an abelian word subgroup `N` has finite atomic joint
spectral PVM at every matrix coordinate while its limiting algebra
`B=W^*(U(N))` is diffuse.  No fixed energy of the form `(FWE1)--(FWE2)` can
distinguish that atomic-to-diffuse escape: its value is forced to converge
to the value in the diffuse limiting representation.  Atomicity, the number
of joint atoms, the least positive atom trace, and the existence of a
positive-trace minimal projection are not detected by fixed word moments.

Apply this to a hypothetical canonical microstate sequence for

```text
Q=EL_5(M_3(L_2(k))).                                   (FWE3)
```

By `ordinary-leavitt-parabolic-atomic-spectrum-is-trivial`, every surviving
marked root must converge through the diffuse part of the full last-column
coefficient vertex.  If the canonical microstates converge to the regular
trace, every fixed mixed Steinberg word energy, every fixed coefficient-word
Gram, and every fixed spherical Hilbert--Schmidt average converges to its
value in `L(Q)`.  Hence none of these fixed quantities is itself a
matrix-only anti-diffusion statistic.

This does **not** rule out using a fixed relator defect after a separate
finite-coordinate decoder has produced discontinuous domains.  For example,
if matrix-only reasoning authenticates projections `P_n^(d)` as common
multiplicity reservoirs, Pythagoras can make one fixed word pay their total
energy.  What the theorem rules out is obtaining those domains from fixed
word moments alone.  A surviving proof must use at least one operation not
preserved by tracial moment convergence, such as:

1. a minimum-atom or finite multiplicity assertion with a uniform positive
   density consequence;
2. a common-factor/matrix-polynomial identity whose degree or selected
   coordinate domain is authenticated before taking the ultralimit; or
3. a depth or word family which grows with the requested accuracy, followed
   by a dimension-free recurrence returning the growing-scale failure to a
   fixed marked carrier.

In particular, the spherical-average bypass cannot close by taking
`X_U` and its orbit frame to be fixed functorial word-polynomial vectors.
Both its contraction and almost-invariance estimates would pass to the
diffuse regular model.  Its unresolved `word-authenticated sector` must
therefore contain exactly the same finite-coordinate authentication that the
global-PVM route calls the anti-diffusion gate.

Proof: `fixed-word-hs-energy-continuity-proof`.
