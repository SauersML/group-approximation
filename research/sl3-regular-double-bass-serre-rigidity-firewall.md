---
rg: 2
id: sl3-regular-double-bass-serre-rigidity-firewall
kind: claim
title: Bass--Serre orthogonality and property T do not internally fold the regular SL3 arithmetic double
artifacts:
  - research/artifacts/sl3-arithmetic-double-regular-trace-firewall-2026-08-21.md
distinct_from:
  sl3-regular-arithmetic-double-fold-mark-collapse: that asks whether canonical matrix microstates collapse the fold mark; this proves that the regular trace, Bass--Serre orthogonality, property T spectral projection, and relative nonamenability alone cannot do so inside a tracial von Neumann algebra.
  sl3-arithmetic-double-finite-representations-fold: that uses finite-dimensional co-density and really does fold exact matrix representations; the regular group factor contains an exact infinite-dimensional counterconfiguration to every trace-internal extension of that argument.
---

Put `B=L(C)`, `P_j=L(i_j(A))`, and

```text
M=L(A *_C A)=P_0 *_B P_1.
```

For `h in A-C`, Bass--Serre reduction gives

```text
tau(i_0(h)i_1(h)^(-1))=0,
||u_(i_0(h))-u_(i_1(h))||_2=sqrt(2).                     (BDF1)
```

On `L^2(M) direct_sum L^2(M)`, let

```text
rho(a)=diag(lambda(i_0(a)),lambda(i_1(a)))
```

and let `V` swap the two summands.  Then `V` commutes exactly with `rho(C)`
but its `h`-commutator has the maximal separation in `(BDF1)`.  Therefore a
property-(T) projection onto the `C`-invariant vectors fixes `V`; it provides
no movement toward an `A`-intertwiner.

Nor can relative amenability supply that movement.  The group `A` has
property (T), `C` has infinite index, and hence the transitive action on
`A/C` is not amenable: an invariant mean would give almost invariant vectors
in `ell^2(A/C)`, property (T) would give an invariant vector, and no nonzero
constant vector lies in `ell^2` of an infinite set.  By the group/subfactor
co-amenability correspondence, `B subset P_j` is not a coamenable inclusion.

Thus all of the named regular-trace and von Neumann algebra data coexist with
an exactly nonfolded mark.  A proof of regular-microstate collapse must use a
finite-coordinate/Connes-embedding obstruction, not a tracial identity,
Kazhdan projection, or relative-amenability argument alone.

