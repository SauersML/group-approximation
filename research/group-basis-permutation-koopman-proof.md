---
rg: 2
id: group-basis-permutation-koopman-proof
kind: route
title: Read the induced action on the canonical group-unitary basis
target: group-basis-actions-have-permutation-koopman-spectrum
requires: []
---

For `k in K`, the canonical unitary `u_k` is the delta vector at `k` in
`L^2(L(K))=l^2(K)`, and the automorphism induced by
`alpha_g in Aut(K)` sends it to `u_(alpha_g(k))`.  These vectors are an
orthonormal basis, proving `(GBK1)`.

If `Phi:D -> L(K)` is normal, trace preserving and equivariant, then

```text
||Phi(x)||_2^2 = tau_K(Phi(x)^* Phi(x)) = tau_D(x^*x).
```

It therefore extends to an isometric intertwiner from `L^2(D)` into
`l^2(K)`, whose range is closed.  This proves the necessary condition for
all equivariant base embeddings, without a Cartan hypothesis.

For the cyclic counterexample, split the countable `Z`-set `K` into orbits.
On an orbit of length `n`, every eigenvalue is an `n`th root of unity.  On an
infinite orbit the action is the bilateral shift on `l^2(Z)`; the equation
`f(m-1)=lambda f(m)` makes `|f|` constant and hence gives no nonzero square-
summable eigenvector.  An irrational circle rotation has the nonzero
eigenfunction `z |-> z` with non-torsion eigenvalue, so no embedding exists.

Finally, `S_fin(N)` is countable, amenable and ICC, hence its group factor is
the hyperfinite `II_1` factor.  Every standard probability algebra is a
separable abelian finite von Neumann algebra and embeds trace-preservingly in
that factor.  This proves that the obstruction is equivariant rather than a
restriction on the measure weights themselves.
