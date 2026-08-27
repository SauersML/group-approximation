---
rg: 2
id: finite-moment-random-relator-sparsification
kind: claim
title: A finite robust relator menu can be sparsified against all matrix dimensions at once
artifacts:
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
---

Fix a finite relator menu `S`, a finite test set `B`, separation `delta>0`,
relator thresholds `0<eps<eps_plus`, and a distribution `mu` on `S`.  Let

```text
W = S union {a^{-1}b : a,b in B, a != b}
```

and let `K_delta` be the compact closure of the `W`-profiles of all
finite-dimensional unitary tuples for which the words in `B` are pairwise
`delta`-separated.  Choose `eta>0` with

```text
2 eta < eps_plus^2 - eps^2
```

and an `eta`-net `Z` of `K_delta`, `|Z|=N`.  For `z in K_delta` put

```text
p(z) = Pr_(r~mu)[ 2 - 2 z_r <= eps_plus^2 ]
```

and suppose

```text
q = sup_(z in K_delta) p(z) < 1.
```

If `m` relators are sampled independently from `mu`, then

```text
Pr[there exists a delta-separated finite-dimensional unitary tuple,
   in any matrix size, on which every sampled relator has d_2-defect <= eps]
 <= N q^m.
```

Consequently, if a presentation-preservation event `SC` for the same sampled
relators has probability `Pr(SC)>N q^m`, then some sampled presentation lies in
`SC` and admits no such separated `eps`-microstate in **any** matrix dimension.

The theorem is a finite union bound after projecting to the compact trace
profile.  It replaces the dimension-by-dimension summability hypothesis in
`unitary-word-return-entropy-summability`.
