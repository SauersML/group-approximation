---
rg: 2
id: stw82-complementary-cutdowns-merge-iff-near-projections
kind: claim
title: Complementary cutdown supports merge asymptotically exactly in the near-projection regime
---

Let `h_n` be positive contractions in unital C*-algebras `B_n`.  The
following are equivalent:

1. there are positive contractions `a_n,b_n` with `a_n b_n=0` and
   `max(norm(a_n-h_n),norm(b_n-(1-h_n))) -> 0`;
2. `norm(h_n(1-h_n)) -> 0`;
3. there are projections `p_n in B_n` with `norm(h_n-p_n) -> 0`.

More quantitatively, if the maximum in (1) is at most `delta`, then

```text
norm(h_n(1-h_n)) <= 2 delta.                          (C1)
```

If `eta=norm(h_n(1-h_n))<1/4`, functional calculus gives a projection
`p_n` satisfying

```text
norm(h_n-p_n)
  <= (1-sqrt(1-4 eta))/2.                            (C2)
```

Accordingly, the raw complementary supports `h_n` and `1-h_n` arising in
the standard quasicentral two-cut construction can be perturbed to
orthogonal supports with vanishing error if and only if the cutdowns are
asymptotically projectional.  Quasicentrality by itself does not enter this
criterion.
