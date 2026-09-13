---
rg: 2
id: fp-simple-algebra-over-finite-field-with-rank-model
kind: claim
title: Some finitely presented infinite-dimensional simple algebra over a finite field has a unital rank model
distinct_from:
  algebra-boone-higman-conjecture: that asks for finitely presented simple envelopes of decidable algebras, built so far from Leavitt tensor hosts, which have halvable corners; this asks for one finitely presented simple algebra with a faithful rank function, which no halvable corner allows.
  sofic-fp-simple-kazhdan-group-from-fp-simple-ring: that is the group target of the ring route; this is its ring gate (a), in the strengthened rank-model form.
---

**OPEN.** There is a finitely presented, infinite-dimensional, simple unital algebra `R` over a
finite field `k` with a unital homomorphism `R -> prod_omega M_(n_i)(k) / {rank-null}`.

**Payoff.** By `rank-modelled-simple-rings-give-linear-sofic-projective-el`,
`S = EL_m(R)/(EL_m(R) ∩ k^x 1)` is infinite, Kazhdan for `m >= 3`, and `k`-linear sofic. It is
the ring input of `sofic-fp-simple-kazhdan-group-from-fp-simple-ring`, where gates (b) and (c)
remain.

**What such an algebra must avoid.**
- **Halvable corners.** A rank function kills them, and every purely infinite simple algebra has
  one (`purely-infinite-simple-algebras-have-nonsofic-el-groups`). So Leavitt, graph, Cuntz–Krieger
  and Nekrashevych algebras are excluded.
- **Exact finite models.** A finitely presented simple LEF ring is finite
  (`lef-simple-rings-are-not-finitely-presented`). So the rank model must be genuinely approximate.
- **Characteristic zero Weyl algebras.** They are not finitely generated rings, and over a finite
  field they are not simple.

## Attempts

- **Free minimal SFT crossed products.** Route
  `fp-simple-rank-model-algebra-via-rigid-free-minimal-sft`. It needs
  `free-minimal-z2-sft-is-quantum-rigid`.
- **Literature status: unknown.** No web search was possible from this lane (search budget
  exhausted). The graph records no finitely presented simple algebra over a finite field with a
  rank function. Every finitely presented simple algebra over a finite field recorded here is purely
  infinite.
