---
rg: 2
id: zaremsky-rips-contractibility-criterion-citation
kind: route
title: Import Zaremsky's discrete Morse criterion for contractible Vietoris–Rips complexes
target: zaremsky-rips-contractibility-criterion
requires: []
---

Citation import, not a reproof. Matthew C. B. Zaremsky, *Contractible
Vietoris-Rips complexes of Z^n*, arXiv:2410.11993 (v1 15 October 2024, v2
12 August 2025, accepted by Proc. Amer. Math. Soc.).

- Property (*): "All distances in X are integers, and for all t ∈ ℕ there
  exists n_t ∈ ℕ such that |S| ≤ n_t for all S ⊆ X with diam(S) = t."
- Theorem 3.1: "Let (X,d) be a metric space satisfying (*). Fix t₀, and
  suppose that for all t>t₀ there exists r_t<t such that every S⊆X with
  diam(S)=t lies in some ball of radius r_t. Assume moreover that for some
  such ball, its center lies within t of the center of any other such ball.
  Then VR_{t₀}(X) is contractible."
- The balls are centred at points of `X`. The proof is Bestvina–Brady discrete
  Morse theory on the full simplex on `X`, with simplices ordered by diameter.
- Corollary 3.2: `VR_t(Z^n)` is contractible for `t ≥ n^2 + n − 1`.

Read from the arXiv abstract page and the HTML rendering on 2026-09-13. The
proof was not re-derived here.
