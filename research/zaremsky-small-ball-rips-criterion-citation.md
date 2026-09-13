---
rg: 2
id: zaremsky-small-ball-rips-criterion-citation
kind: route
title: Import Theorem 3.1 of Zaremsky, Contractible Vietoris-Rips complexes of Z^n
target: small-ball-criterion-gives-contractible-rips-complexes
requires: []
---

Citation import. M. C. B. Zaremsky, *Contractible Vietoris–Rips complexes of `Z^n`*,
arXiv:2410.11993v2 (dated August 14, 2025). Read from the arXiv PDF on 2026-09-13
(pages 1–5).

- Convention (p. 1): "`VR_t(X)` is the simplicial flag complex with vertex set `X` such
  that vertices span a simplex whenever they are pairwise within distance `t` of each
  other."
- Standing assumption (p. 3), verbatim: "(*): All distances in `X` are integers, and for
  all `t ∈ N` there exists `n_t ∈ N` such that `|S| ≤ n_t` for all `S ⊆ X` with
  `diam(S) = t`."
- **Theorem 3.1** (p. 3), verbatim: "Let `(X, d)` be a metric space satisfying (*). Fix
  `t_0`, and suppose that for all `t > t_0` there exists `r_t < t` such that every
  `S ⊆ X` with `diam(S) = t` lies in some ball of radius `r_t`. Assume moreover that for
  some such ball, its center lies within `t` of the center of any other such ball. Then
  `VR_{t_0}(X)` is contractible (as is `VR_t(X)` for all `t > t_0`)."

The proof (p. 4) applies Bestvina–Brady discrete Morse theory to the height
`h(S) = diam(S) − (|S| − 1)/n_{diam(S)}` on the barycentric subdivision of `VR_∞(X)`,
and shows each descending link is contractible, using a standard nerve lemma in the
case where no point of `S` is a centre. The lane read the proof but did not re-derive
the Morse lemma it cites (Zaremsky, Amer. J. Math. 144 (2022), Corollary 1.11).
Corollary 3.2 of the same paper reproves Virk's theorem for `Z^n` at scales
`t ≥ n^2 + n − 1`.
