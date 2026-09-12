---
rg: 2
id: finite-edge-attachments-residual-decouple
kind: claim
title: Finite-edge attachments tensor-decouple from every unbounded residual quotient tower
distinct_from:
  residual-action-can-erase-local-reynolds-density: that is an abstract matrix-algebra calculation assuming an uncontrolled residual action; this constructs exact representations of an arbitrary group amalgam from genuine finite quotients and computes both endpoint and old-commutant densities.
  finite-affine-head-cannot-retain-old-commutant-density: that specializes the mechanism to the Toeplitz universal lattice and the three-channel affine S3 endpoint; this gives the general amalgam theorem explaining why every attachment through the finite edge alone fails.
---

Let `Gamma` have finite quotients `Q_n` with `|Q_n|->infinity`, let `K` be a
finite group, and let `C` be any group containing `K`.  Suppose
`eta:C->U(V)` is a fixed nonzero finite-dimensional unitary representation.
Embed `K` as the second factor of `Gamma x K` and form

```text
G=(Gamma x K) *_K C.                                   (FED1)
```

Then `G` has exact finite-dimensional representations `rho_n` on

```text
H_n=V tensor ell^2(Q_n)                                (FED2)
```

such that

```text
rho_n(g,k)=eta(k) tensor lambda_n(g_bar),
rho_n(c)=eta(c) tensor I.                              (FED3)
```

Here `lambda_n` is the left-regular representation of `Q_n` and `g_bar` is
the image of `g`.  In particular,

```text
dim End_(Gamma x K)(H_n)/dim(H_n)^2
 =dim End_K(V)/(dim(V)^2 |Q_n|) -> 0,                 (FED4)

dim End_C(H_n)/dim(H_n)^2
 =dim End_C(V)/dim(V)^2>0.                            (FED5)
```

More generally, if `p in C[C]` acts under `eta` as a nonzero projection, its
normalized Hilbert mass in `rho_n` is the fixed positive number

```text
rank eta(p)/dim(V),                                    (FED6)
```

even though the old compressor commutant density in `(FED4)` vanishes.

Consequently no theorem using only the fixed endpoint representation,
identification along `K`, and relations internal to the two vertex groups can
place a positive-density endpoint multiplicity algebra in the old
`Gamma x K` commutant.  A successful trace-promotion cell must include an
ordinary relation involving a nontrivial `Gamma` coefficient word outside
the finite edge, or recurse inside the residual quotient algebra that causes
the factor `1/|Q_n|`.

