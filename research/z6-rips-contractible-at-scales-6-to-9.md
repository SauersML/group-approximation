---
rg: 2
id: z6-rips-contractible-at-scales-6-to-9
kind: claim
title: The Rips complex of Z^6 in the l^1 metric is contractible at scales 6, 7, 8 and 9
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem, contractibility of every Rips complex of Z^n at scales r ≥ n^2(2n−1); this claim covers the small scales r = 6..9 for n = 6, below every published general bound
---

For `r ∈ {6, 7, 8, 9}`, the Vietoris--Rips complex `VR(Z^6, d_1; r)` is contractible. Here `d_1` is the
standard word metric, and a finite set spans a simplex iff its diameter is at most `r`.

Context. Zaremsky's conjecture says that `VR(Z^n, d_1; r)` is contractible for all `r ≥ n`.
Gupta–Sarkar–Shukla (arXiv:2511.04238, Theorems 1.2–1.3) prove it for `n ≤ 5`, and for `n = 6` with
`r ≥ 10`. They leave `n = 6`, `6 ≤ r ≤ 9` open. Together with their Theorem 1.3, this claim gives
Zaremsky's conjecture for `n = 6`.

The proof is a computer certificate, checked by an independent verifier. It is a single uniform
domination and link-collapse sequence on the peeling-link vertex set `Lmax` that leaves only
`e_1, …, e_6`: route `z6-rips-contractible-at-scales-6-to-9-proof`.
