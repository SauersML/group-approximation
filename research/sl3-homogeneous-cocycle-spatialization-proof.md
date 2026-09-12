---
rg: 2
id: sl3-homogeneous-cocycle-spatialization-proof
kind: route
title: Compress the right-lattice crossed product and tensor covariant implementers with the regular representation
target: sl3-homogeneous-ce-is-common-cocycle-spatialization
requires:
  - dense-s-arithmetic-translation-algebra-is-amplified-profinite
---

Equal finite trace of `q` and `alpha_g(q)` in the semifinite factor `Q`
gives the partial isometries `v_g`.  Direct multiplication shows that the
maps and unitaries in `(HCS1)` obey

```text
beta_g beta_h=Ad(c(g,h)) beta_(gh),
c(g,h)c(gh,k)=beta_g(c(h,k))c(g,hk),                    (HCSP1)
```

so they form a cocycle action on `B=qQq`.

Let `u_g` be the canonical right-lattice unitary in
`Q rtimes_alpha Lambda'` and put

```text
W_g=v_g u_g in q(Q rtimes_alpha Lambda')q.
```

Then

```text
W_g x W_g^*=beta_g(x),          W_gW_h=c(g,h)W_(gh).    (HCSP2)
```

Fourier expansion, exactly as for a compressed ordinary crossed product,
gives a trace-preserving isomorphism

```text
q(Q rtimes_alpha Lambda')q = B rtimes_(beta,c) Lambda'. (HCSP3)
```

By `(DT2)`, the algebra on the left is a nonzero finite full corner of the
amplification of `L^infinity(G/Lambda') rtimes A`.  Connes embeddability is
invariant under amplification and nonzero corners, so `(HCS2)` is equivalent
to Connes embeddability of `(HCSP3)`.

If `(HCSP3)` embeds trace preservingly into `R^omega`, restrict the embedding
to `B` and take the images of the `W_g`.  Equations `(HCSP2)` become `(HCS3)`.

Conversely suppose `(HCS3)` holds.  On algebraic twisted Fourier terms set

```text
x |-> pi(x) tensor 1,
W_g |-> U_g tensor lambda(g),                            (HCSP4)
```

where `lambda` is the left regular representation of `Lambda'`.  Equations
`(HCS3)` give covariance and the twisted multiplication in `(HCSP2)`.  The
regular Fourier labels make `(HCSP4)` trace preserving, hence faithful, and
it extends to `(HCSP3)`.  The lattice `Lambda'` is residually finite (it is a
finitely generated linear group in characteristic zero), so `L(Lambda')` is
Connes embeddable.  Tensor-product permanence therefore makes the separable
range of `(HCSP4)` Connes embeddable.  This proves the converse.

For the final gauge assertion in the target, both `U_gU_h` and
`pi(c(g,h))U_(gh)` implement the same automorphism
`pi beta_g beta_h pi^(-1)` of `pi(B)`.  Their quotient `Z_(g,h)` therefore
commutes with `pi(B)`.  No covariance equation forces that quotient to be
the identity; the second line of `(HCS3)` is precisely the missing condition.
