---
rg: 2
id: arithmetic-star-packet-carrier
kind: claim
title: The affine compressor carries a finitely presented S9 star packet with a nontrivial marked commutator
distinct_from:
  arithmetic-star-packet-non-mf: This is only the algebraic carrier, finite action quotient, and nontrivial mark; that endpoint additionally applies the operator-norm packet-collapse theorem.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
---

Let `P=Gamma(3) ltimes Z^3`, let `alpha(g,v)=(g,2v)`, and put
`H=alpha(P)`.  On `X=P/H` and one extra point `star`, set

```text
K=Sym(X union {star})=S_9,       k=(H star).
```

Let `P` act on `K` through its coset action, put `A=K rtimes P`, let `E` be
the ascending HNN extension with `tPt^(-1)=H`, and form `W=A *_P E`.
Then `W` is finitely presented.  The subgroup `H` fixes `k`, while the
certified `p_0 notin H` moves it, so `[p_0,k]!=1` in `A` and in `W`.

Modulo two, the images of `P` and `H` on the eight cosets are respectively
`AGL(3,2)` and its point stabilizer `GL(3,2)`, of orders `1344` and `168`.

