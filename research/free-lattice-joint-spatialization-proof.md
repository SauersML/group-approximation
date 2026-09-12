---
rg: 2
id: free-lattice-joint-spatialization-proof
kind: route
title: Proof that rank-one CE is simultaneous spatialization of the finite-corner return action
target: free-lattice-ce-is-joint-ultrapower-spatialization
requires:
  - dense-s-arithmetic-translation-algebra-is-amplified-profinite
---

Let `P` be the semifinite factor in `(DT1)`, with its trace-preserving action
`alpha:F_r -> Aut(P)`, and let `q` have finite nonzero trace.  Equal trace in
a semifinite factor gives `(FJS1)`.  If `u_s` is the canonical implementing
unitary in `P rtimes_alpha F_r`, then

```text
W_s=v_su_s in q(P rtimes_alpha F_r)q                         (PJS1)
```

is a unitary and `Ad(W_s)|_(qPq)=beta_s`.  Because there are no relations
among the free generators, the `W_s` define a unitary representation of
`F_r`, while the `beta_s` define an honest action.  The Fourier map therefore
gives

```text
q(P rtimes_alpha F_r)q  isomorphic to  (qPq) rtimes_beta F_r. (PJS2)
```

For completeness, `(PJS2)` is onto, not merely an inclusion.  If `g in F_r`,
write the corresponding product as `W_g=v_gu_g`, where
`v_g^*v_g=alpha_g(q)` and `v_gv_g^*=q`.  Every compressed Fourier term has
the form

```text
q x u_g q=(q x alpha_g(q)v_g^*)W_g,                         (PJS3)
```

and the coefficient in parentheses belongs to `qPq`.  Conditional
expectations show that the map is trace preserving and faithful.

By `(DT2)`, `P rtimes_alpha F_r` is the amplification of the finite
homogeneous-quotient factor `M`.  Hence `M` is Connes embeddable exactly when
the finite full corner in `(PJS2)` is.

Suppose first that `(qPq) rtimes_beta F_r` embeds trace preservingly into
`R^omega`.  Restrict the embedding to `qPq` and take the images of the
canonical free-generator unitaries.  These are one `pi` and the simultaneous
`U_s` in `(FJS3)`.

Conversely, suppose `(FJS3)` holds.  Freeness extends `s |-> U_s` to a
homomorphism `phi:F_r -> U(R^omega)`.  On algebraic Fourier terms define

```text
x |-> pi(x) tensor 1,
w_g |-> phi(g) tensor lambda(g),                            (PJS4)
```

where `lambda` is the left regular representation.  Covariance follows from
`(FJS3)`.  The `lambda(g)` Fourier coefficients show that `(PJS4)` preserves
the canonical trace and is injective.  Its separable generated range lies in
a tensor product of Connes-embeddable tracial algebras, hence is Connes
embeddable.  This proves the converse.

Finally fix one generator `s`.  The group `Z` is amenable, so the crossed
product of the Connes-embeddable finite algebra `qPq` by `beta_s` is Connes
embeddable (amenable crossed-product permanence; equivalently Gao,
Theorem 3.1, arXiv:2012.07940).  Applying the forward implication to this
cyclic crossed product produces an embedding `pi_s` and one implementer.
Nothing in that argument makes the embeddings `pi_s` independent of `s`.
That missing common choice is exactly the simultaneous condition `(FJS3)`.
