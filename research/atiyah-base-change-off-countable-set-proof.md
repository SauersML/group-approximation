---
rg: 2
id: atiyah-base-change-off-countable-set-proof
kind: route
title: Diagonalize over the central polynomial ring of the division closure and count eigenvalues of companion matrices
target: atiyah-base-change-holds-off-a-countable-set
requires: []
artifacts:
  - research/artifacts/atiyah-countable-exceptions-2026-09-12.md
---

Complete argument in `research/artifacts/atiyah-countable-exceptions-2026-09-12.md`,
Sections 2 and 3. Outline:

1. **Skew field.** Linnell's criterion (Schick, arXiv:math/0001101v3,
   Lemma 3.4, quoted in `atiyah-passes-to-torsion-free-elementary-amenable-extensions`)
   makes `D = D_(Qbar[G])` a skew field. `D[x]`, with `x` central, is left and
   right Euclidean. Jacobson's normal form gives
   `P A(x) Q = diag(f_1..f_r) (+) 0` with `P, Q` invertible over `D[x]`.
2. **Specialization.** Evaluation `x -> z` is a ring homomorphism
   `D[x] -> U(G)`, since scalars are central. Hence
   `dim ker A(z) = (n - r) + sum_i dim ker f_i(z)`, and
   `dim ker f_i(z) = dim ker(z - C_i)` for the companion matrix `C_i` of the monic
   part of `f_i`.
3. **Countability.** Eigenspaces of `C_i` for distinct eigenvalues are
   independent submodules of `U(G)^(l_i)`, so their dimensions sum to at most
   `l_i`. Only countably many `z` carry a kernel. There are countably many
   families, so `E_G` is countable.
4. **Embedding.** For transcendental `z` outside `E_G`, every nonzero `f in D[x]`
   has a linear representation `f(x) = U(x) B^-1 V` over `Qbar[G][x]`. The Schur
   complement turns `f(z)` into a family that does not jump at `z`, so `f(z)` is
   invertible. By Ore's universal property `D(x)` embeds in `U(G)` as the
   division closure of `Qbar(z)[G]`.
5. **Invariance.** Invariance forces the value at every transcendental `z` to
   equal the value at a non-exceptional one. Conversely, an empty `E_G` makes
   every transcendental value `n - r(A)`.
6. **Several variables.** The kernel dimension is a Borel function of the
   parameters. Repeat steps 1-4 over `D(x_1..x_(s-1))`, then apply Fubini and
   Kuratowski--Ulam. QED
