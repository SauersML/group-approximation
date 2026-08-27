---
rg: 2
id: signed-monomial-tracial-images-are-sofic
kind: claim
title: Every tracial image represented by signed monomial coordinates is sofic
distinct_from:
  block-monomial-coordinate-collapse: that extracts a permutation model from block-monomial models of a specific wreath product; this is the elementary metric equivalence for arbitrary signed permutation coordinates and their tracial GNS group image.
  slofstra-natural-negative-corner-image-is-sofic: that proves soficity for one spectral-corner image by analyzing its particular permutation construction; this gives a general signed-monomial criterion with no corner or solution-group input.
  faithful-mf-models-realize-all-mf-traces: that changes norm-faithful matrix coordinates without changing a prescribed limiting trace; this identifies when the GNS group quotient of the prescribed trace is sofic.
---

**ESTABLISHED SIGNED-MONOMIAL CRITERION.** Let `G` be countable and let

```text
rho_n:G -> B_(d_n)
```

be asymptotic homomorphisms in normalized Hilbert--Schmidt norm, where
`B_d` is the finite signed permutation group (the monomial matrices with
entries in `{+1,-1}`).  Let `N` be their tracial kernel,

```text
N={g: ||rho_n(g)-1||_(2,d_n) ->_omega 0}.              (SMT1)
```

Then `G/N` is sofic.

Indeed, let `j_d:B_d->Sym({1,...,d} times {+1,-1})` be the faithful action

```text
U e_i=epsilon_i e_(sigma(i))
        ==> j_d(U)(i,s)=(sigma(i),epsilon_i s).          (SMT2)
```

For all `U,V in B_d`,

```text
d_H(j_d(U),j_d(V))
 <= (1/2)||U-V||_(2,d)^2
 <= 2 d_H(j_d(U),j_d(V)).                              (SMT3)
```

Thus the signed-monomial HS ultraproduct and the doubled-set permutation
ultraproduct have exactly the same identity kernel.  Composing the
`rho_n` with `j_(d_n)` therefore gives an injective homomorphism

```text
G/N -> product_omega(Sym(2d_n),d_H),                    (SMT4)
```

which is a sofic model.

This applies equally when the original maps are exact homomorphisms from a
free presentation and each fixed defining relator becomes the identity
eventually.  Such maps first define a homomorphism of the presented group
into the signed-monomial metric ultraproduct, and `(SMT3)` preserves its
kernel after passage to permutations.

DERIVATION
signed-monomial-hs-hamming-comparison-proof
