---
rg: 2
id: two-external-return-cell-has-finite-s3-model
kind: claim
title: The first commuting two-external-return cell retains the S3 Whitehead gauge
invalidates:
  - two-external-returns-kill-s3-gauge
artifacts:
  - research/two-external-return-s3-proof.md
distinct_from:
  native-weyl-return-gauges-have-s3-model: that uses one external return and the opposite root in its Weyl expansion; this adds a distinct commuting external normalizer and a literal L0 Steinberg triangle containing it.
  one-singer-square-does-not-identify-external-return-gauge: that leaves two independent commuting qubit gauges after one transport; this retains the noncommuting S3 Whitehead/return pair after native two-return commutation and a same-carrier triangle.
---

**ESTABLISHED TWO-RETURN FIREWALL.**  The enumeration uses source-to-target
arrows but matrix roots `x_(target,source)`.  Thus the external arrow
`9->5` is

```text
n=x_78(1),                 r=x_59(1),                  (TRS1)
```

not `x_95(1)`.  The two matrices commute.  The signed-Hecke generators
contain the arrows `5->4` and `9->4`, namely the matrix roots

```text
x_45(1),x_49(1) in L_0,                                (TRS2)
```

and the literal Steinberg triangle is

```text
[x_45(1),x_59(1)]=x_49(1).                             (TRS3)
```

This genuinely places the second return in a native triangle on the same
signed carrier.  On the one-character carrier `Q`, both `L_0` roots have
identity reservoir factor.  If `E` is the multiplicity involution of `n`
and `G` that of `r`, the reservoir parts of `(TRS3)` and commutation are

```text
[1,G]=1,                       [E,G]=1.                 (TRS4)
```

The triangle does not determine `G`: it occurs once and once inversely
inside a commutator whose other leg is scalar.  More importantly, neither
row says `[D,E]=1`, where `D` is the Whitehead/Weyl gauge.

The exact finite model from `native-weyl-return-gauges-have-s3-model`
therefore extends by

```text
D=(1 2),       E=(2 3),       F=(1 3),       G=E.      (TRS5)
```

Here `F` is the opposite-root gauge in the native Weyl word.  The old rows

```text
D=EFE,                    F=DED,              (DE)^3=1 (TRS6)
```

remain exact, `(TRS4)` holds, `D!=E`, and `DE` remains a nonidentity
three-cycle.

All Singer and fixed-Weyl translates extend without changing the result:
assign every transported occurrence its literal conjugate.  The `L_0`
roots retain identity gauge, while `E,G` receive the same conjugation.
Every mixed square is then the same product on both paths.  No transported
copy creates `[D,E]=1`.

The same fence applies whenever a commuting second return participates
only in triangles whose other input and output lie in the signed scalar
packet: its gauge cancels inside those triangle commutators instead of
being identified with `D`.  A successful row must put `D` itself into a
commutation relation with `E`, or give a second braid length incompatible
with the surviving order-three product.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature result, or local
compilation is used.

## Attempts

- **Use native commutation of `n,r`.**  It imposes `[E,G]=1`, exactly
  realized by `G=E`; it contains no information about `D`.
- **Use the literal `L_0` triangle.**  Its other input and output are scalar
  on `Q`, so the occurrence of `G` cancels and is not authenticated.
- **Add all Singer conjugates.**  They conjugate `G=E` by the same stage
  gauges.  Naturality supplies no equality between that conjugate and `D`.

DERIVATION
two-external-return-s3-proof

