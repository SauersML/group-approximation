---
rg: 2
id: fpbs-relative-threshold-continuous-at-co-amenability-proof
kind: route
title: Expected-boundary version of the Schreier Folner trifurcation count, a mass transport for uniqueness transfer, and lifting Folner sets through amenable extensions
target: fpbs-relative-threshold-continuous-at-co-amenability
requires:
  - fpbs-co-amenable-subgroup-relative-threshold-is-pc
  - fpbs-cluster-count-trichotomy
  - fpbs-relative-gap-along-any-subgroup-separates
  - fpbs-quotient-l2-threshold-sandwich
---

Notation is that of the target and of
`fpbs-co-amenable-subgroup-relative-threshold-is-pc-proof`, cited below as
[CA]. `X = I\Gamma`, `pi(x) = Ix`, and fibres are `I`-orbits.

## Item 1. Quantitative transfer

Fix `p in (p_c(G), p_u(G))` with `delta(p) > p h(I)`. Choose a finite nonempty
`F ⊆ X` with `|∂F| / |F| < delta(p)/p`, which exists by the definition of
`h(I)`.

1. **Steps 1–2 of [CA]** apply verbatim, since they never use co-amenability.
   They give the zero-one law for `A_I` and `P_p(x in T) = delta(p)` at every
   vertex `x`.
2. **Hypothesis H** (for contradiction): a.s. every cluster meets every fibre
   finitely. Put `W = pi^(-1)(F)` and define `xi`, `C(x)` and `b(x)` as in
   Step 3 of [CA]. Finiteness of `C(x)`, the identity `|∂C| = sum_(x in C) b(x)`
   and the counting lemma `|T ∩ C| <= |∂C|` are proved there without
   co-amenability.
3. **Expected boundary.** The only change is to replace the deterministic
   bound on `b` by its expectation. For `x = x_phi in D`:
   - the edges at `x` leaving `W` are the `{x, xs}` with `phi s ∉ F`;
   - distinct `s` give distinct neighbours `xs`, so distinct edges;
   - each edge is open with probability `p`.

   So `E b(x_phi) = p #{s : phi s ∉ F}`, and summing gives
   `sum_(x in D) E b(x) = p |∂F|`.
4. **Step 4 of [CA]** (Lemma 4 and the two transports `f` and `g`) uses `b`
   only through `sum_(x in D) E b(x)`. So it gives

   ```text
   delta(p) |F|  <=  sum_(x in D) E b(x)  =  p |∂F|  <  delta(p) |F| ,
   ```

   a contradiction. So H fails at `p`.
5. **Step 5 of [CA]** (sprinkling onto `I`) then gives `P_(p')(A_I) > 0` for
   every `p' > p`, and hence `P_(p')(A_I) = 1` by the zero-one law. So
   `p_c(I;G) <= p`.

Taking the infimum over such `p` gives `p_c(I;G) <= p_tri(h(I))`. If no such
`p` exists, then `p_tri = p_u(G)`, and `p_c(I;G) <= p_u(G)` holds by
`fpbs-relative-gap-along-any-subgroup-separates`. `QED`

The Remark "Sharpness of the method" in [CA] records `delta <= h`. The correct
form of that bound is `delta <= p h`, which is what item 1 inverts.

## Item 2. Continuity

- `p_c(G) <= p_c(I_k;G)` always holds.
- If `p_c(G) = p_u(G)`, then `p_c(I_k;G) <= p_u(G) = p_c(G)`.
- Otherwise fix any `p in (p_c,p_u)`. Then `delta(p) > 0` by Step 2 of [CA],
  and `h(I_k) < delta(p)/p` for all large `k`. So `p_c(I_k;G) <= p` by item 1.

Since `p` was arbitrary, `limsup p_c(I_k;G) <= p_c(G)`. `QED`

## Item 3. Uniqueness transfer

Let `N <= M` be infinite, and let `p` be such that a.s. exactly one cluster
`C*` meets `M` infinitely. It suffices to show that a.s. `|C* ∩ N| = infinity`.
Then `A_N` holds at `p`, and `p_c(N;G) <= p`.

1. **Equivariance.** For `n in M`, `nM = M` and left multiplication maps
   clusters to clusters. So `C*(n omega) = n C*(omega)`.
2. **Constant positive density on M.** For `m in M`,
   `P(m in C*(omega)) = P(e in C*(m^(-1) omega)) = P(e in C*)`. Since
   `|C* ∩ M| = infinity` a.s., `E|C* ∩ M| = infinity`, so `P(e in C*) > 0`.
3. **Zero-one.** The event `{|C* ∩ N| < infinity}` is invariant under left
   multiplication by `N`. `N` is infinite and acts freely on vertices, so it
   is mixing on the Bernoulli edge measure (as in Step 1 of [CA]). Hence the
   event has probability 0 or 1.
4. **Mass transport on N.** Suppose the probability is 1. Put
   `X = C* ∩ N`, a.s. finite, with `X(n omega) = n X(omega)` for `n in N`. On
   `N x N` put `f(x,y) = 1{y in X} / |X|`, and `0` when `X` is empty. Then
   `f(nx, ny)(n omega) = f(x,y)(omega)`, so the mass-transport principle for
   the countable group `N` gives
   `sum_y E f(e,y) = sum_x E f(x,e)`.
   - The left side is `P(X nonempty) <= 1`.
   - The right side is `E[ 1{e in X} sum_(x in N) 1/|X| ] = infinity`, since
     `N` is infinite and `P(e in X) = P(e in C*) > 0` by step 2.

   This is a contradiction. So `|C* ∩ N| = infinity` a.s. `QED`

With `M = N = I` this gives `p_c(I;G) <= p_u(I;G)`, which is the first
inequality of `fpbs-relative-gap-along-any-subgroup-separates`. With `M = Gamma`
it gives `p_c(N;G) <= p_u(G)`.

## Item 4. Cheeger invariance under amenable extension

Put `Q = Gamma/N`, `L = M/N`, normal in `Q`, and `Q/L = Gamma/M`. Let
`psi : Q -> Gamma/M` be the quotient map. `Gamma` acts on both spaces by right
multiplication through `S`, and `psi` is equivariant. For finite `E` and
symmetric `S`,

```text
sum_(s in S) |E s Δ E|  =  sum_s ( |E \ E s^(-1)| + |E \ E s| )  =  2 |∂E| .
```

**`h(M) <= h(N)`.** Let `E ⊆ Q` be finite. Put `u = psi_* 1_E`, so
`u(phi) = |E ∩ psi^(-1)(phi)|`. By equivariance, `psi_*(1_E . s) = u . s`.
Pushforward is an `ℓ^1` contraction, so
`sum_s ||u.s - u||_1 <= sum_s |E s Δ E| = 2|∂E|`, while `||u||_1 = |E|`.
The layer-cake step (steps 4–6 of Lemma 0 in [CA]) gives a level set `F`
with `2|∂F| = sum_s |F s Δ F| <= (2|∂E|/|E|) |F|`. So
`h(M) <= |∂E|/|E|`.

**`h(N) <= h(M)`.** Let `F' ⊆ Gamma/M` be finite and `epsilon > 0`.
1. Fix a section `sigma : Gamma/M -> Q`. For `phi in F'` and `s in S` write
   `sigma(phi) s = c(phi,s) sigma(phi s)` with `c(phi,s) in L`. There are
   finitely many values of `c`.
2. `L` is amenable, so there is a finite nonempty `A ⊆ L` with
   `|A c Δ A| <= epsilon |A|` for each of these values `c`.
3. Put `E = { l sigma(phi) : l in A, phi in F' }`. Then `|E| = |A||F'|`.
4. The element `l sigma(phi) s = l c(phi,s) sigma(phi s)` lies outside `E`
   only if either `phi s ∉ F'`, or `phi s in F'` and `l c(phi,s) ∉ A`.
   For each pair `(phi,s)` the second case happens for at most
   `|A c Δ A| <= epsilon |A|` values of `l`.
5. So `|∂E| <= |A||∂F'| + epsilon |A||F'||S|`, and
   `|∂E|/|E| <= |∂F'|/|F'| + epsilon |S|`.

Since `epsilon` is arbitrary, `h(N) <= h(M)`. `QED`

## Item 5. The sandwich

- `p^Q(N) = p^Q(M)` is part 2 of `fpbs-quotient-l2-threshold-sandwich`
  (amenable-extension invariance).
- `p^Q(M) <= p_c(M;G)` is its lower bound.
- `p_c(M;G) <= p_c(N;G)` holds because `N ⊆ M`: a cluster meeting `N`
  infinitely meets `M` infinitely.
- `p_c(N;G) <= p_tri(h(N)) = p_tri(h(M))` follows from items 1 and 4.
- `p_c(N;G) <= p_u(M;G)` follows from item 3.

The localisation of a C4 counterexample is the contrapositive of item 1 at
`I = N`, with `h(N) = h(M)`. `QED`

## Remark: why cutting cannot separate N from M

A proof of C4, `p_c(N;G) <= p_c(M;G)`, by cutting at a level
`p in (p_c(M;G), p_c(N;G))` would need an `N`-invariant cut `W` with finitely
many `N`-orbits and expected boundary below `delta(p) |W/N|`.
- By item 4, the best available ratio is `p h(N) = p h(M)`. This is the same
  number for `N` and for `M`.
- A cut inside one `M`-coset, `W = psi^(-1)(F)` with `F` Folner in `L`, pays
  `p |S \ M|` per vertex. Branches leave `M` and re-enter at far `N`-cosets,
  so sprinkling back onto one `N`-coset is unavailable.

The invariant that blocks the method is `h(Gamma/M) > 0`. The step where it
dies is Step 4 of [CA], which yields only `delta <= p h`.
