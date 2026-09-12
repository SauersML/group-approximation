---
rg: 2
id: infinite-index-canonical-subgroup-corner-is-impossible
kind: claim
title: A finite crossed product has no positive canonical corner for an infinite-index stabilizer
distinct_from:
  coinduction-preserves-but-cannot-create-algebraic-envelope: that computes the zero-trace vacuum tail in product coinduction; this is the action-independent finite-trace obstruction behind that computation.
  algebraic-compact-action-envelope-for-non-ce-relation: that allows arbitrary non-Cartan embeddings; this rules out only the canonical subgroup-corner implementation and therefore does not refute the envelope target.
---

Let a countable group `Lambda` act trace-preservingly on a finite von Neumann
algebra `(B,tau)`, let `M=B rtimes Lambda`, and let `H<Lambda` have infinite
index.  There is no nonzero projection `p in B` satisfying

```text
alpha_h(p)=p                    for h in H,
p u_g p=0                      for g notin H.             (ISC1)
```

Consequently an infinite-index subgroup crossed product cannot be isolated
as the canonical positive-trace base-coset corner of a probability crossed
product.  In particular, coset/wreath modules cannot import a non-CE
`B_0 rtimes H` merely by replacing the characteristic projection of the
induced coset with a positive-Haar projection.  Any surviving envelope must
be a genuine non-Cartan inclusion whose image is not obtained by cutting the
canonical `Lambda` Fourier unitaries down to `H`.
