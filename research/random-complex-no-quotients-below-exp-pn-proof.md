---
rg: 2
id: random-complex-no-quotients-below-exp-pn-proof
kind: route
title: Run Meshulam's first moment over simple groups at general p
target: random-complex-group-no-quotients-below-exp-pn
requires: []
---

Notation and the two inputs are from R. Meshulam, *Bounded quotients of the
fundamental group of a random 2-complex*, arXiv:1308.3769v1, read from the PDF
on 2026-09-12.
- Fix a finite group `G`. `C^1` is the set of `G`-valued 1-cochains on the
  complete graph, and `C^0` acts on it by gauge transformations.
- `||[φ]||` is the minimum support size in the orbit of `φ`.
- `||d_1 φ||` is the number of triangles `{u,v,w}` with
  `φ(u,v)φ(v,w)φ(w,u) != 1`.

1. **Quotients and cohomology** (Meshulam, Claim 2.1 and Corollary 2.2).
   `Hom(π_1(Y), G)/G ↔ H^1(Y;G)`, and `[φ] ∈ H^1(Y;G)` iff `d_1 φ = 1` on every
   triangle of `Y`. A nontrivial finite quotient `Q` of `π_1(Y)` has a simple
   quotient `G` with `1 < |G| <= |Q|`, which gives a nontrivial class in
   `H^1(Y;G)`.

2. **Expansion of the simplex** (Meshulam, Proposition 3.1).
   `||d_1 φ|| >= (n/3) ||[φ]||` for every group `G`. For a vertex `u`, put
   `φ_u(v) = φ(u,v)` (and `φ_u(u) = 1`). Then
   `d_1 φ(u,v,w) = (φ_u . φ)(v,w)`, so

   ```text
   6 ||d_1 φ|| = sum_u 2 ||φ_u . φ|| >= 2 n ||[φ]||.
   ```

3. **First moment at general `p`.** A class is a cocycle on `Y` iff every
   triangle in its violation set is absent. That has probability
   `(1-p)^(||d_1 φ||) <= exp(-pn ||[φ]||/3)`. An orbit of weight `k` has a
   representative supported on `k` edges, so there are at most
   `C(C(n,2),k) |G|^k` such orbits. With `r_G = (n^2/2) |G| exp(-pn/3)`,

   ```text
   Pr[ H^1(Y;G) != {[1]} ] <= sum_{k>=1} r_G^k <= 2 r_G     whenever r_G <= 1/2.
   ```

4. **Union over simple groups.** There are at most two non-isomorphic finite
   simple groups of each order (Artin's theorem on orders of simple groups,
   completed by the classification; Kimmerle--Lyons--Sandling--Teague, Proc.
   London Math. Soc. (3) 60 (1990) 89--122). Meshulam uses the same count,
   `|G(N)| <= 2N`, on p. 6. Take `N = exp(pn/8)`.
   - For `|G| <= N`, `r_G <= (n^2/2) exp(-5pn/24) -> 0`.
   - Hence

   ```text
   Pr[ some nontrivial finite quotient of order <= N ]
       <= sum_{G simple, 1<|G|<=N} 2 r_G
       <= 2N . n^2 N exp(-pn/3)
       =  2 n^2 exp(-pn/12)  ->  0,
   ```

   because `pn - 24 log n -> infinity`. ∎

**Relation to the import.** At `p = (6+7c) log n / n` this is Meshulam's own
computation (his display (2)). Nothing in steps 1--4 uses that particular `p`.
The mid-range import `meshulam-random-complex-no-polynomial-quotients` got its
polynomial bound through monotone coupling. Running the count at `p` directly
gives order `exp(n^η/8)`.
