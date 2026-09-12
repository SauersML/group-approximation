---
rg: 2
id: haagerup-factor-stripping-proof
kind: route
title: Apply Haagerup Fourier multipliers and Popa intertwining to the rigid subfactor
target: haagerup-factor-direction-strips-from-property-t-envelope
requires: []
---

Because the actions commute, the `Gamma`-action extends from `B` to
`P=B rtimes H` by fixing the canonical `H`-unitaries, and `(HFS1)` holds.
Choose normalized positive-definite functions

```text
phi_n in c_0(Gamma),   phi_n(g) -> 1
```

given by the Haagerup property.  On finite Fourier sums in `M=P rtimes
Gamma`, define

```text
Phi_n(sum_g x_g u_g) = sum_g phi_n(g) x_g u_g.          (HFS3)
```

These are normal unital trace-preserving completely positive maps, converge
pointwise to the identity in `L^2`, and are compact relative to `P`.  The
last assertion can be read directly: on `L^2(M)=direct_sum_g L^2(P)u_g`,
`Phi_n` is diagonal with scalar entries `phi_n(g)`; truncating the `c_0`
function to finite support approximates it in operator norm by a finite sum
of `P`-finite Fourier-coordinate maps.

Since `Q` has property `(T)`, the inclusion `Q subset M` is rigid.  Therefore
the pointwise convergence in `(HFS3)` is uniform on the unit ball of `Q`:

```text
sup_(v in U(Q)) ||Phi_n(v)-v||_2 -> 0.                  (HFS4)
```

Suppose `Q` did not intertwine into `P`.  Popa's intertwining criterion would
give unitaries `v_j in U(Q)` such that

```text
||E_P(x v_j y)||_2 -> 0       for every x,y in M.       (HFS5)
```

For a finite-support Fourier multiplier, `(HFS5)` makes the `L^2`-norm of
its value on `v_j` tend to zero coefficient by coefficient.  Approximation
of `phi_n` in sup norm by finite-support functions then gives, for every
fixed `n`,

```text
||Phi_n(v_j)||_2 -> 0.                                  (HFS6)
```

Choose `n` so large that the supremum in `(HFS4)` is below `1/2`.  Since
`||v_j||_2=1`, `(HFS4)` gives `||Phi_n(v_j)||_2>1/2` for all `j`, contradicting
`(HFS6)`.  This proves `(HFS2)`.

Intertwining supplies nonzero projections `q in Q`, `p in M_m(P)` and a
normal star-homomorphism

```text
theta:qQq -> p M_m(P) p
```

implemented by a nonzero partial isometry.  Since `Q` is a factor, `theta`
is injective.  If `P` were Connes embeddable, so would be its matrix
amplification, the corner `pM_m(P)p`, and the subfactor `theta(qQq)`.
Connes embeddability of a nonzero corner of a `II_1` factor implies Connes
embeddability of the factor, contradicting the hypothesis on `Q`.  Hence
`P` is non-CE.  For Haar compact-abelian `B`, Fourier transform identifies
`P` trace-preservingly with `L(A rtimes H)`, giving the application.
