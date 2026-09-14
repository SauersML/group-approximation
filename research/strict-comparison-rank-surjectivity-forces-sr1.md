---
rg: 2
id: strict-comparison-rank-surjectivity-forces-sr1
kind: claim
title: Strict comparison plus surjective rank map forces stable rank one
distinct_from:
  stw58-simple-pure-k1-bijective: that uses Lin's pure dichotomy to get K1-bijectivity for pure algebras; this is Lin's sharper theorem that surjectivity of the rank map alone, under strict comparison, gives stable rank one and tracial approximate oscillation zero.
  stw63-strict-comparison-sr1-uniqueness: that assumes stable rank one and strict comparison to get uniqueness of Jiang--Su embeddings; this derives stable rank one from strict comparison and rank surjectivity.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `A` be a sigma-unital non-elementary simple C*-algebra that is not purely
infinite, has a nonzero quasitrace, and has strict comparison. Then the
canonical map

```text
Gamma : Cu(A) -> LAff_+(QT~(A)),    Gamma([a])(tau) = d_tau(a),
```

is surjective if and only if `A` has tracial approximate oscillation zero.
If either holds, `A` has stable rank one.

For unital separable exact `A`, surjectivity of `Gamma` is exactly the
conclusion "all ranks occur" of STW Problem XXIII. So under strict comparison
a counterexample to K1-injectivity is automatically a counterexample to the
Rank Problem.
