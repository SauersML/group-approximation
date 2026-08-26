---
rg: 2
id: binary-jacobson-balanced-shift-transport-is-xor
kind: claim
title: The balanced Jacobson shift transports raw roots by triangular XOR rows, not by a square Toeplitz arrow
distinct_from:
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for a matrix-selected same-square inverse pair; this computes the literal first monomial/raw-root occurrence and shows that it supplies only a symmetric-difference projection identity.
  finite-weyl-root-moments-do-not-authenticate-toeplitz-square: that gives an abstract rectangular model for every finite typed Weyl/root language; this computes the exact native Jacobson conjugation formulas at the generation seam.
---

**ESTABLISHED.**  Put `Q=1-ST` and, on two coordinate rows, let

```text
a=[[S,Q],[0,T]],             a^(-1)=[[T,0],[Q,S]].     (JXT1)
```

The element `a` belongs to the monomial-symbol preimage and has Laurent
symbol `diag(z,z^(-1))`.  For every third coordinate `k` and `r in J`,

```text
Ad(a)x_1k(r)=x_1k(Sr),
Ad(a)x_2k(r)=x_1k(Qr)x_2k(Tr),                         (JXT2)
Ad(a)x_k1(r)=x_k1(rT),
Ad(a)x_k2(r)=x_k1(rQ)x_k2(rS).                         (JXT3)
```

The two factors in each product commute.  In particular

```text
Ad(a)x_2k(1)=x_1k(Q)x_2k(T).                           (JXT4)
```

For any unitary representation and involution `g`, write
`p_g=(1-rho(g))/2`.  Equation `(JXT4)` gives only

```text
rho(a)p_(x_2k(1))rho(a)^*
 = p_(x_1k(Q)) triangle p_(x_2k(T)),                   (JXT5)
```

and hence the rank identity

```text
rank(p_b)=rank(p_h)+rank(p_d)-2 rank(p_h p_d).         (JXT6)
```

The independent regular profile satisfies `(JXT6)` exactly.  Thus the first
literal monomial/raw-root transport does not itself give a strict Hall
deficit, rank loss, or same-square inverse pair.  A successful decoder needs
an additional authenticated occurrence which orients this XOR row.
