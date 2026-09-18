---
rg: 2
id: gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings-proof
kind: route
title: Direct proof with lattice classes in Q_p^(n+1), following Serre's Trees
target: gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings
requires:
  - divisible-elements-act-elliptically-on-trees
---

Direct proof. Not independently reviewed. Write `V = Q_p^(n+1)`, `N = n + 1`, and
`v_p` for the `p`-adic valuation. Inputs from Serre, *Trees*, Ch. II §1.1: for
`N = 2` the lattice classes form a `(p+1)`-regular tree, and its ends correspond to
the lines of `V`.

## Part 1

Every lattice is `g Z_p^N` for some `g in GL_N(Q_p)`, so `X_p` is a quotient of
`GL_N(Q_p)/GL_N(Z_p)`. That set is countable, since `GL_N(Z_p)` is an open
subgroup of the σ-compact group `GL_N(Q_p)`.

**Faithfulness.** Let `g in GL_N(Q_p)` fix every class. Take any `v != 0`, extend
it to a basis `v, w_2, ..., w_N`, and for `k >= 0` put
`M_k = Z_p v + p^k (Z_p w_2 + ... + Z_p w_N)`. Then `g M_k = λ_k M_k` for some
`λ_k in Q_p^x`.

- **Scalars.** Compare Haar volumes. `vol(g M) = |det g|_p vol(M)` for every
  lattice `M`, and `[M_0 : M_k] = p^(k(N-1))`, so
  `vol(g M_k)/vol(g M_0) = p^(-k(N-1))`. The left side is also
  `|λ_k|_p^N vol(M_k) / (|λ_0|_p^N vol(M_0))`. Hence `|λ_k|_p = |λ_0|_p`, so
  `λ_k = λ_0 u_k` with `u_k in Z_p^x`, and `λ_k M_k = λ_0 M_k`.
- **Eigenvector.** Put `h = λ_0^-1 g`. Then `h M_k = M_k` for all `k`, and so does
  `h^-1`. As `∩_k M_k = Z_p v`, both `h v` and `h^-1 v` lie in `Z_p v`, so
  `h v in Z_p^x v`.

So every nonzero vector is an eigenvector of `g`, and `g` is scalar. So
`PGL_N(Q_p)` acts faithfully on `X_p`.

## Part 2

If `[diag(g, 1)]` is trivial, `diag(g, 1) = μ I`; the last entry gives `μ = 1`, so
`g = I`. For `x -> ax + b`, `[[a, b], [0, 1]] = μ I` forces `a = 1`, `b = 0`.
`PGL_N(Q) -> PGL_N(Q_p)` is injective, since a matrix with rational entries that is
a `Q_p`-scalar is a rational scalar. Faithfulness on `X_p` is then Part 1.

## Part 3

The stabilizer in `PGL_N(Q_p)` of `[L]` is the image of `Q_p^x · GL(L)`. That is
`GL(L)/Z_p^x`, which is compact and open, hence profinite. The vertex stabilizers
of a subgroup `Γ <= PGL_N(Q_p)` are its intersections with these, so they are
subgroups of profinite groups, which are residually finite. For `Γ = PGL_2(Q)` on
`T_(p+1)`, part 3 of `divisible-elements-act-elliptically-on-trees` says the
unipotent `(Q,+)` fixes exactly one end and no vertex. It fixes the line
`Q_p e_1`, so that end is the one corresponding to `Q_p e_1`.

## Part 4

- **Transitivity.** `GL_N(Q)` is dense in `GL_N(Q_p)`, since `Q` is dense in
  `Q_p`. Vertex stabilizers in `GL_N(Q_p)` are open, and `GL_N(Q_p)` is transitive
  on lattices, so `GL_N(Q)` is transitive on `X_p`.
- **Pairs.** For lattices `L, M`, write `M = g L` with elementary divisors
  `p^(a_1), ..., p^(a_N)` of `M` relative to `L`. The number
  `δ([L],[M]) = max a_i - min a_i` is well defined on classes, invariant under
  `GL_N(Q_p)`, and unbounded (take `M = diag(p^k, 1, ..., 1) L`). So there are
  infinitely many orbits on pairs.
- **Stabilizers.** The stabilizer of `[Z_p^N]` in `PGL_N(Q)` is the image of
  `GL_N(Z_(p))`, where `Z_(p) = Q ∩ Z_p` (scale by a power of `p` to make
  `λ = 1`). The map `[g] -> det g mod (Z_(p)^x)^N` is well defined on it, and it
  is onto `Z_(p)^x/(Z_(p)^x)^N`. As `Z_(p)^x ~ {±1} x ⊕_(q != p) Z`, that quotient
  is an infinite group of exponent dividing `2N`, so it is not finitely generated,
  and neither is the stabilizer. By transitivity, every vertex stabilizer is
  conjugate to this one.
