---
rg: 2
id: position-window-ucp-section-folner-no-go-proof
kind: route
title: Apply the trivial character to the window identity and read off equality in Cauchy-Schwarz
target: position-window-ucp-sections-collapse-to-folner-vectors
requires: []
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

Let `epsilon:C^*(Lambda)->C` be the trivial character (the integrated form of
the trivial representation; it exists for every discrete group) and put

```text
chi := epsilon o q : C^*(Gamma) -> C,                        (PWP1)
```

the trivial character of `C^*(Gamma)`.  `chi` is a unital `*`-homomorphism, so
it is multiplicative and satisfies `chi(a^*)=conj(chi(a))` and
`chi(u_gamma)=1` for every `gamma in Gamma`.  Set

```text
z_g := chi(c_g) in C,     z=(z_g)_(g in Lambda),
```

a finitely supported vector in `l^2(Lambda)`.

**Normalization.**  Applying `chi` to `sum_g c_g^* c_g = 1` gives

```text
sum_g |z_g|^2 = 1,   i.e.  ||z||_2 = 1.                      (PWP2)
```

**The window identity collapses.**  Applying `chi` to `(PW1)` and using
`chi(m(g,k))=1` (each `m(g,k)` is a group word):

```text
chi(s(u_k)) = sum_g conj(z_g) z_(gk) = <z, R_k z>,           (PWP3)
```

where `R` is the right regular representation of `Lambda` on `l^2(Lambda)`,
`(R_k z)(g)=z(gk)`.  On the other hand `chi = epsilon o q`, so the hypothesis
`q(s(u_k))=u_k` gives

```text
chi(s(u_k)) = epsilon(u_k) = 1.                              (PWP4)
```

**Exact case.**  Combining `(PWP2)`-`(PWP4)`, `<z,R_k z> = 1 = ||z|| ||R_k z||`.
Equality in Cauchy--Schwarz forces `R_k z = lambda z` with `|lambda|=1`, and
the value `1` of the inner product forces `lambda=1`, so `R_k z = z` for every
`k in K`.  Since `K` generates `Lambda`, `z` is invariant under the whole right
regular representation, hence constant on `Lambda`.  A constant vector in
`l^2(Lambda)` with `Lambda` infinite is `0`, contradicting `||z||=1`.  This is
`(PW2)`.

**Approximate case.**  If `||q(s(u_k))-u_k|| <= delta` then
`|chi(s(u_k))-1| = |epsilon(q(s(u_k))-u_k)| <= delta`, so
`Re <z,R_k z> >= 1-delta` and

```text
||R_k z - z||^2 = 2 - 2 Re <z,R_k z> <= 2 delta.
```

`Lambda` is infinite, so the regular representation has no nonzero invariant
vector; if `(Lambda,K)` has Kazhdan constant `kappa` then
`max_(k in K) ||R_k z - z|| >= kappa ||z|| = kappa`, whence
`kappa^2 <= 2 delta`.  This is `(PW3)`.

**Two extensions, free from the same proof.**  (i) The index set may be
`Gamma` rather than `Lambda`, with the reindexing `g |-> g sigma(k)`: the exact
case then only needs `Gamma` infinite, which holds for `Gamma=G_0` virtually
free and infinite.  (ii) The middle factors need not be group words; it is
enough that `chi(m(g,k))=1`, which covers every convex combination of group
elements, so smoothing the window over several words does not help either.

**The finite face is the exact boundary.**  If `Lambda` is replaced by a
*finite* group `P`, `(PWP3)`-`(PWP4)` still force `R_p z = z` for all `p`, but
now `z=|P|^(-1/2) 1_P` satisfies this, and it is precisely the vector produced
by the explicit section of
`explicit-finite-face-ucp-section-is-edge-equivariant`.  So this route does not
merely fail to refute that node -- it predicts it, and identifies infiniteness
of the target group as the single hypothesis separating the two.
