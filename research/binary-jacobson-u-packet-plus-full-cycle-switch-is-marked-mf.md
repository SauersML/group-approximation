---
rg: 2
id: binary-jacobson-u-packet-plus-full-cycle-switch-is-marked-mf
kind: claim
title: The mixed Jacobson compression packet and its full-cycle switch remain marked MF until the opposite root is retained separately
artifacts:
  - research/binary-jacobson-u-packet-plus-full-cycle-switch-proof.md
distinct_from:
  binary-jacobson-balanced-center-fold-data-is-finite-marked: that proves the packet P itself is finite; this adjoins the composite full-cycle switch and x_23(T), obtaining an infinite but amenable marked subsystem.
  binary-jacobson-full-cycle-weyl-switches-residual-sign: that computes the orthogonal carrier switch; this proves that all word data used by that switch still admits regular-profile marked MF models.
  binary-jacobson-first-alternating-ts-closure-relation: that retains x_31(1) as a separate occurrence in order to form x_21(T); this shows that keeping x_21(T), x_23(T), and only the composite Weyl switch loses precisely that load-bearing occurrence.
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that treats the full monomial-symbol preimage; this treats a nonmonomial but parabolic Laurent-symbol subgroup.
---

**ESTABLISHED.**  Let

```text
A=F_2[t,t^(-1)],
mu:EL_5(J)->EL_5(A)
```

be the Laurent symbol map.  Retain the finite balanced-center packet

```text
P=<w,v,d,X,u,C,l>
```

of `binary-jacobson-balanced-center-fold-data-is-finite-marked`, where in
particular

```text
w=x_13(Q),       d=x_13(S^2T),
u=x_21(T),       l=x_41(T).
```

Let `omega` be the full-cycle Weyl switch from
`binary-jacobson-full-cycle-weyl-switches-residual-sign`, and put

```text
tau=x_23(T),             H=<P,omega,tau>.                (JPA1)
```

Then `H` is amenable.  Its canonical regular character is MF, and the head
`w=x_13(Q)` is nontrivial in `H`.  Consequently there are operator-norm
asymptotic unitary representations `sigma_n` of `H` whose normalized traces
converge pointwise to the regular character.  If `w_hat_n` denotes the
rounded involution associated to `sigma_n(w)`, then

```text
rank((1-w_hat_n)/2)/d_n -> 1/2.                          (JPA2)
```

Thus the entire balanced `u`-compression package, the composite full-cycle
switch, and the exposed root `x_23(T)` have a positive-density marked-MF
counterprofile.  No universal square decoder or sparse PI contradiction can
follow from only these occurrences.

The distinction between a composite word and its typed constituents is
load-bearing.  The separately evaluated opposite root

```text
k=x_31(1)
```

lies outside the amenable symbol parabolic below.  Hence a continuation of
the alternating-closure route must retain and compress `k` itself; replacing
it by the already evaluated composite `omega` loses the first displayed
occurrence which crosses this firewall.

