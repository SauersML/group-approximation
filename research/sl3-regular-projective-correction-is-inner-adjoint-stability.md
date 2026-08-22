---
rg: 2
id: sl3-regular-projective-correction-is-inner-adjoint-stability
kind: claim
title: Canonical projective correction for SL3 is exactly inner-adjoint normalized-HS stability
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that asks for correction to projective odd-congruence models and permits flexible corners; this identifies the exact same-dimension metric and the nonlinear inner-adjoint constraint, without asserting correction.
  character-rigidity-equals-hyperfinite-hs-stability: that corrects hyperfinite-limit almost representations through character theory; this concerns the nonamenable regular-character limit and requires corrected adjoint representations to remain inner.
  kazhdan-weak-ucp-stability-is-flexible-stability: that converts arbitrary dilation correction to finite-dimensional flexible correction for Kazhdan groups; this is the stricter inner-adjoint subvariety relevant to projective commutators.
---

Let `d>=1`, give `End(M_d)` its normalized Hilbert--Schmidt norm, and let
`U,V in U(d)`.  The conjugation operators satisfy the exact identity

```text
||Ad(U)-Ad(V)||_(2,End(M_d))^2
 =2(1-|tr_d(U*V)|^2).                                  (IAS1)
```

If

```text
d_proj(U,V)=min_(z in T)||U-zV||_(2,d),
```

then

```text
d_proj(U,V)^2=2(1-|tr_d(U*V)|),
d_proj(U,V)^2 <= ||Ad(U)-Ad(V)||_2^2
                 <=2 d_proj(U,V)^2.                    (IAS2)
```

Consequently a same-dimension matrix microstate `sigma_n` is close,
generator by generator and modulo phases, to a projective representation
`rho_n` if and only if `Ad(sigma_n)` is normalized-HS close to the honest
representation `Ad(rho_n)` **inside the inner-conjugation locus**.
Conversely, if an honest representation on `M_(d_n)` has the form
`g mapsto Ad(rho_n(g))`, multiplicativity says

```text
rho_n(g)rho_n(k)rho_n(gk)^(-1) in T 1,
```

so `rho_n` is projective.  Thus this is an equivalence, not merely a
one-way reduction.

The canonical trace hypothesis is preserved by this operation:

```text
tr_(End(M_d))(Ad(sigma_n(g)))=|tr_d(sigma_n(g))|^2.     (IAS3)
```

Hence regular-character microstates remain regular-character microstates
after adjointing.  Their limiting GNS algebra is nevertheless
`L(SL_3(Z))`, not a hyperfinite algebra.  Ordinary normalized-HS stability
of the adjoint tuple to an arbitrary representation on the `d_n^2`-
dimensional Hilbert space is insufficient: the corrected representation
need not consist of inner automorphisms of `M_(d_n)`.

There is also no selected-vector estimate from normalized-HS closeness of
arbitrary superoperators.  On an `N`-dimensional Hilbert space, the identity
and the reflection in one unit vector have normalized-HS distance
`2/sqrt(N)` but differ by `2` on that vector.  In the commutant-transfer
problem the selected vector is precisely the unitary `U_n in M_(d_n)`.
Therefore property (T) cannot use an arbitrary adjoint correction unless
innerness, or a stronger selected-vector/operator-norm estimate, is retained.
