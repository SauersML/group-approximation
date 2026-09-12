---
rg: 2
id: finite-s6-selector-centralizer-pins-common-pivot-arm
kind: claim
title: A fixed S4 selector centralizer pins one common-pivot arm in S6
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that forces the filling area of commutators with one finite-order mark to grow as the centralizer correction escapes through infinitely many Schreier cosets; this uses one fixed six-letter packet and three fixed selector commutators, so no address or coset tends to infinity.
  depth-three-r5-selector-pays-a6-label-flip: that uses one selector chosen for the particular wrong label; this packages three selectors into one fixed subgroup which simultaneously detects every possible wrong common-pivot arm.
  a5-a4-overlap-has-two-seam-charges: that concerns nonuniqueness of representation extension across an A4 face; this is a group-element centralizer and character gap after the local six-letter packet has been jointly exactified.
---

Let

```text
Omega={i,p,j,k,l,q},              Delta={j,k,l,q},
K=Sym(Delta)=<(j k),(k l),(l q)> < S(Omega).                     (FSC1)
```

Then

```text
C_(S(Omega))(K)=Sym({i,p})={1,(i p)}.                             (FSC2)
```

For `x in Omega setminus {p}`, put `s_x=(x p)` and let

```text
Z={(j k),(k l),(l q)}.
```

For every finite-dimensional unitary representation `pi` of `S(Omega)`,

```text
||pi(s_x)-pi(s_i)||_2^2
 <= sum_(z in Z) ||[pi(s_x),pi(z)]-I||_2^2.                       (FSC3)
```

Indeed `(FSC3)` is equality `0=0` for `x=i`.  For every `x in Delta`, at
least one edge `z in Z` is incident to `x`.  Then both

```text
s_i^(-1)s_x              and              [s_x,z]
```

are three-cycles, hence conjugate in `S(Omega)`, and the corresponding term
on the right of `(FSC3)` equals the left side by character invariance.

If the common pivot is `r=(p q)`, set `t_x=s_x^r` and
`c_x=s_x t_x` in the Bleak--Quick right-action convention.  The same estimate
also gives

```text
||pi(c_x)-pi(c_i)||_2
 <=2 (sum_(z in Z)||[pi(s_x),pi(z)]-I||_2^2)^(1/2).               (FSC4)
```

Thus a fixed three-selector packet kills every finite label-permutation
gauge at once.  The result is dimension-free and compatible with direct sums;
trivial and sign summands cause no exception because all transpositions have
the same image there.

