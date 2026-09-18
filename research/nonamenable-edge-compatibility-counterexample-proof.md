---
rg: 2
id: nonamenable-edge-compatibility-counterexample-proof
kind: route
title: Bell--Rogalski free generators in the quantum-plane Ore field, lifted to a free group algebra over k0(lambda) by Lichtman's valuation corollary, give F2 whose closure already contains the central lambda
target: nonamenable-edges-break-division-ring-compatibility
requires: []
---

**Imported.**
- **Sanchez**, arXiv:1206.7013, the paragraph before Proposition 2. The Ore field of `k[H3]` with
  `H3 = <x, y | [x,y] central>` is `k`-isomorphic to the Ore field `Q` of `K[X; sigma]`, with `K = k(lambda)(t)` and
  `t^sigma = lambda t`. The isomorphism is `lambda -> [x,y]`, `t -> x`, `X -> y`.
- **Bell--Rogalski**, arXiv:1101.5829, Theorem 2.2, in the form of Sanchez, Theorem `teo:bell`.
  - Let `F/k` be a field extension, `sigma` in `Aut_k F`, and `Q` the Ore field of `F[X; sigma]`.
  - Suppose `b` is in `F \ F_sigma`, and for every `f` in `F`, `f^sigma - f` in `F_sigma + F_sigma b` implies `f` in `F_sigma`.
  - Then `(1-X)^-1` and `b(1-X)^-1` freely generate a free `k`-subalgebra of `Q`.
- **Lorenz-type lemma**, Sanchez Lemma `le:lorenz`, which follows Lorenz.
  - Let `lambda` in `k^x` not be a root of unity, with `t^sigma = lambda t` on `k(t)`.
  - Let `g` be in `k(t) \ k[t]` with a unique pole, and let that pole be nonzero.
  - Then `f^sigma - f` in `k + kg` implies `f` in `k`.
  - The first paragraph of its proof shows `F_sigma = k`, via Laurent series.
- **Lichtman**, J. Algebra 90 (1984) 516--527, Corollary 1 on p. 524, as applied by Sanchez in the proof of Theorem 1.
  - Let `D` be a division ring with a discrete valuation `nu` trivial on a central subfield `k`.
  - Suppose `x, y` freely generate a free `k`-subalgebra, with `nu(x) = 1` and `nu(y) = 2`.
  - Then `1 + x` and `1 + y` freely generate a free group `k`-algebra.
  - Sanchez applies it with exactly these valuations. The statement was not re-checked against Lichtman's paper.

**Setup.**
- Let `k0` be a field, `l = k0(lambda)` with `lambda` transcendental, `K = l(t)`, and `sigma(t) = lambda t`.
- Let `Q` be the Ore field of `K[X; sigma]`. Then `lambda` is central in `Q`, since `sigma` fixes `l`.
- `lambda` is not a root of unity in `l`.

**1. A free `l`-subalgebra.**
- Apply le:lorenz over the base field `l` to `g = (1-t)^-1`. It is not a polynomial, and its only pole is `t = 1`,
  which is nonzero.
- So `f^sigma - f` in `l + l g` implies `f` in `l`, and `F_sigma = l`. Also `g` is not fixed by `sigma`, since its
  pole moves to `lambda^-1`.
- Bell--Rogalski with `k = l` and `b = g` then gives: `p = alpha = (1-X)^-1` and `q = g alpha` freely generate a free
  `l`-subalgebra `A` of `Q`.

**2. A second pair of free generators, with valuations 1 and 2.**
- `p' = p - 1` and `q` also freely generate `A`, since `p -> p - 1` is an automorphism of the free algebra.
- Put `x = p'` and `y = p' q p'`.
- A word `x^(i0) y x^(i1) y ... y x^(in)` expands to the single monomial
  `p'^(i0+1) q p'^(i1+2) q ... q p'^(in+1)`, or to `p'^(i0)` if there is no `y`.
- The number of `q` factors recovers `n`, and the exponents recover the `i_j`. So distinct words give distinct
  monomials, and `x, y` freely generate a free `l`-subalgebra.
- Let `nu` be the `X`-adic valuation on `Q`: zero on `K^x`, with `nu(X) = 1`. It exists because `sigma` preserves `K`,
  so `K[X; sigma]` is graded by `X`-degree.
- `x = alpha - 1 = X(1-X)^-1` has `nu(x) = 1`.
- `nu(g) = 0` and `nu(alpha) = 0`, so `nu(y) = 1 + 0 + 0 + 1 = 2`.

**3. A free group algebra.**
- By Lichtman's corollary over the central field `l`, `u = 1 + x = alpha` and `v = 1 + y` freely generate a free
  group `l`-algebra in `Q`.
- In particular `<u, v>` is free of rank 2, and `l[F2] -> Q`, `a -> u`, `b -> v`, is injective.

**4. The closure of `k0[C]` is `Q`.**
- Let `E = Div_Q(k0[u^+-1, v^+-1])`.
- `X = 1 - u^-1` is in `E`.
- `x = u - 1` and `y = v - 1` are in `E`, so `q = x^-1 y x^-1 = g alpha` is in `E`.
- Hence `g = q u^-1` is in `E`, and so is `t = 1 - g^-1`.
- From `tX = X t^sigma = X lambda t` we get `lambda = X^-1 t X t^-1`, which is in `E`.
- So `E` contains `k0(lambda, t) = K` and `X`. It therefore contains `K[X; sigma]`, and so `E = Q`.

**5. `k0[V]` embeds.**
- Let `V = <a,b> x <w>`. Since `lambda` is central, `a -> u`, `b -> v`, `w -> lambda` defines a group homomorphism
  `V -> Q^x`, and so a ring homomorphism `phi: k0[V] -> Q`.
- Write an element as `sum_c sum_n c_(c,n) c w^n`, with `c` in `C` and `c_(c,n)` in `k0`. Its image is
  `sum_c (sum_n c_(c,n) lambda^n) c(u,v)`.
- The coefficients `sum_n c_(c,n) lambda^n` lie in `l`. By step 3 they all vanish.
- Since `lambda` is transcendental over `k0`, every `c_(c,n) = 0`. So `phi` is injective.
- By step 4, `phi` is epic, and `Div(phi(k0[C])) = Q`.

**6. Dependence.**
- `{w^n : n in Z}` is a right transversal of `C` in `V`.
- In `Q`, `1 * phi(w) + (-lambda) * phi(w^0) = 0`, and the coefficients `1` and `-lambda` lie in `Div(k0[C]) = Q`.
- So the transversal is left-dependent over the closure of `C`.
- Consequently `phi` is not Linnell. Since `V` is locally indicable, Linnell is equivalent to Hughes-free
  (Grater, Cor. 8.3), so `phi` is not Hughes-free either.

**7. The graph-of-groups consequence.**
- Let `G = V *_C V'`, with `V' = C x <w'>`. Then `G = C x (<w> * <w'>) = F2 x F2`, and `w != w'` in `G`.
- Give both vertices the embedding `phi`. The edge closures are both `Q`, so the rings are compatible over
  `D_C = Q`.
- The Cohn coproduct `Q *_Q Q = Q`, and the induced `k0[G] -> Q` sends `w - w'` to `lambda - lambda = 0`. So it is
  not injective.
- Thus the construction "coproduct of arbitrary vertex division rings over the edge closures" fails for the
  non-amenable edge `F2`.

**Why amenable edges are different.**
- If `C` is amenable, `Div(k[C])` is the Ore localisation (Tamari).
- A left relation over `Div(k[C])` among transversal elements clears to a common left denominator. This gives a
  relation over `k[C]`, which is impossible because `k[V]` is a free `k[C]`-module on the transversal.
- By Bartholdi, non-amenable `C` has non-Ore `k[C]`, so no such clearing is available. Steps 4--6 show that it
  genuinely fails.
