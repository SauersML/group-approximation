---
rg: 2
id: free-action-covariant-models-contain-the-crossed-product-proof
kind: route
title: Kill the off-diagonal trace on displaced pieces, identify the generated algebra with the crossed product, and pad by a Bernoulli shift
target: free-action-covariant-models-contain-the-crossed-product
requires:
  - support-covariant-models-carry-fixed-point-trace
  - kun-thom-nonsofic-wreath
---

Write `e_A = e(1_A)`.

**Step 1 (item 1, off-diagonal coefficients vanish).** Fix `g != 1`. Essential freeness means
`mu(Fix g) = 0`. Let `(U_k)` be a countable family of Borel sets that separates points. For `x` with
`g x != x`, some `U_k` or its complement contains `x` and not `g x`. As in Step 1 of
`support-covariant-models-carry-fixed-point-trace-proof`, this gives disjoint Borel sets `D_k`
covering `X` up to the null set `Fix g`, with `g D_k ∩ D_k = ∅`. That step uses no covariance and no
support axiom. For `f` supported in a set `A` with `g A ∩ A = ∅`, covariance and the trace property
give

```text
tau(e(f) pi(g)) = tau(e(f) e_A pi(g)) = tau(e_A pi(g) e(f)) = tau(e_A e(f o g^-1) pi(g)) = 0,
```

because `f o g^-1` is supported in `g A`, which is disjoint from `A`. Write
`f = sum_k f 1_(D_k)`, with weak-* convergence of bounded partial sums. Normality of `e` and of
`x -> tau(x pi(g))` then gives `tau(e(f) pi(g)) = 0` for every `f in L^infinity(X)`.

**Step 2 (item 1, identification).** Let `A_0` be the `*`-algebra spanned by `e(f) pi(g)`. It is closed
under products and adjoints by covariance. By Step 1 and trace preservation of `e`,

```text
tau(e(f) pi(g)) = delta_(g,1) integral f dmu,
```

which is the crossed-product trace on `f u_g`. So `f u_g -> e(f) pi(g)` is a trace-preserving
`*`-homomorphism from the algebraic crossed product onto `A_0`. Faithful traces on both sides make it
isometric for the `L^2`-norms. It therefore extends to a unitary between the GNS spaces that intertwines
the left actions. So it extends to a normal trace-preserving isomorphism
`L^infinity(X) ⋊ Gamma ≅ A_0'' <= M`.

**Step 3 (item 2, Bernoulli padding).** Let `Gamma` be infinite, `Z = {0,1}^Gamma` with the fair
product measure `nu`, and `(g z)_h = z_(g^-1 h)`. Fix `g != 1`. Left multiplication by `<g>` on
`Gamma` is free, so it has infinitely many orbits, each of size at least 2. Choose `h_1, h_2, ...` in
distinct orbits. The events `z_(h_i) = z_(g^-1 h_i)` involve disjoint pairs of coordinates, so they are
independent, each of probability `1/2`. Their intersection, which contains `Fix_Z g`, is null. Hence
`Fix_(Y × Z) g ⊆ Y × Fix_Z g` is null for the diagonal action, which is therefore essentially free.
If `Y` is ergodic, then `Y × Z` is ergodic, because a Bernoulli shift of an infinite group is mixing
and hence weakly mixing, and the product of an ergodic action with a weakly mixing one is ergodic.

The first-coordinate projection is equivariant and measure-preserving, so `L^infinity(Y)` sits in
`L^infinity(Y × Z)` as a `Gamma`-invariant subalgebra with the same integral. The crossed-product
trace `f u_g -> delta_(g,1) integral f` restricts to the crossed-product trace of `Y`. So
`f u_g -> f u_g` extends, as in Step 2, to a trace-preserving embedding
`L^infinity(Y) ⋊ Gamma -> L^infinity(Y × Z) ⋊ Gamma`.

**Step 4 (item 3).**
- (c) ⟹ (a): the crossed product `(L^infinity(X) ⋊ Gamma, tau, g -> u_g, f -> f)` is a covariant model.
- (a) ⟹ (b) is immediate.
- (b) ⟹ (c): if `Gamma` is finite, `L^infinity(Y) ⋊ Gamma` is injective (Connes), hence hyperfinite and
  CE. If `Gamma` is infinite, apply (b) to the free action `Y × Z` of Step 3. By Step 1 its CE model
  contains `L^infinity(Y × Z) ⋊ Gamma`, and by Step 3 that contains `L^infinity(Y) ⋊ Gamma`.
  Connes embeddability passes to von Neumann subalgebras with the restricted trace.

The ergodic variant is the same argument, using the ergodic clause of Step 3.

**Step 5 (Kun--Thom consequence).** Let `G`, `Gamma` be the Theorem E pair of `kun-thom-nonsofic-wreath`.
`G` is residually finite, hence hyperlinear.
- Put `A = ⊕_(G/Gamma) Z/2`, with Pontryagin dual `{0,1}^(G/Gamma)` and Haar measure the fair product
  measure. The Fourier transform `L(A) ≅ L^infinity({0,1}^(G/Gamma))` sends `lambda(a)` to the
  character `x -> (-1)^(<a,x>)` and the trace to the integral. It intertwines the coset-permutation
  action of `G`.
- Hence `L(W) = L(A ⋊ G) ≅ L^infinity({0,1}^(G/Gamma)) ⋊ G` trace-preservingly, for
  `W = (Z/2) wr_(G/Gamma) G`.
- If Q1 holds for `G`, item 3(c) makes this crossed product CE. So `L(W)` is CE and `W` is hyperlinear.
- `W` is nonsofic by Theorem A. The free action used in (b) ⟹ (c) is `{0,1}^(G/Gamma) × {0,1}^G`,
  which is exactly the Kun--Thom free nonsofic action of `kun-thom-free-nonsofic-action`.
