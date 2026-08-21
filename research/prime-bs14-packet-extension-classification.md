---
rg: 2
id: prime-bs14-packet-extension-classification
kind: claim
title: Exact primitive-prime scalar BS14 packets extend iff they are the full odd Weil orbit
distinct_from:
  iwahori-cycle-packet-determinant-fence: that gives a necessary determinant congruence; this gives the complete exact classification for primitive prime-order scalar packets.
  iwahori-weil-cycle-packets-extend-exactly: that proves the positive direction for the full odd Weil orbit; this also proves that no other primitive-prime scalar packet extends.
  bs14-relative-involution-extension-stability: that is an approximate flexible-repair theorem over arbitrary sums; this is an exact irreducible packet classifier.
---

Let `p>=7` be prime, let `lambda` be a primitive `p`-th root, and let

```text
m=ord_p(4),
S=diag(lambda,lambda^4,...,lambda^(4^(m-1))),
R(e_j)=e_(j-1),  R(e_0)=v e_(m-1)                  (PBC1)
```

be a scalar BS(1,4) cycle packet.  There is a unitary involution `X` making
`(X,R,S)` an exact solution of the five Iwahori relations if and only if

```text
p = 3 mod 4,
ord_p(4)=(p-1)/2,
v=1.                                                 (PBC2)
```

## Proof

Because `S^p=1`, `iwahori-mod-p-quotient-is-psl2` makes an exact extension a
nontrivial representation of `PSL_2(F_p)`.  The standard complex character
table of `PSL_2(F_p)` gives its smallest nontrivial degree as

```text
(p+1)/2  for p=1 mod 4,
(p-1)/2  for p=3 mod 4.                              (PBC3)
```

Since `4` is a square, `m` divides `(p-1)/2`.  Equation `(PBC3)` rules out
`p=1 mod 4`; in the other congruence class it forces
`m=(p-1)/2`.  Moreover the projective diagonal element `r` has order `m` in
`PSL_2(F_p)`, so `R^m=I` and hence `v=1`.  Conversely, under `(PBC2)` the
odd Weil constituent restricts to exactly `(PBC1)`, as proved in
`iwahori-weil-cycle-packets-extend-exactly`.

Thus the exact zeros seen at `p=7,11,19,23,47` are not numerical accidents,
and the determinant exclusions at primes `p=1 mod 4` are part of a complete
prime-packet classification.
