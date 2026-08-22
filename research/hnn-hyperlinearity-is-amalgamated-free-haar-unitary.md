---
rg: 2
id: hnn-hyperlinearity-is-amalgamated-free-haar-unitary
kind: claim
title: The co-dense HNN group is hyperlinear iff some matrix model of the base carries a Haar unitary in the subgroup centraliser that is free from the base with amalgamation over the subgroup factor
distinct_from:
  hnn-route-is-relative-commutant-collapse: that reduces non-hyperlinearity of the HNN group to the relative-commutant collapse, a SUFFICIENT condition; this records the exact EQUIVALENT condition, amalgamated free independence of one Haar unitary, and shows the collapse and the projective transfer both overshoot it.
  sl2-half-stability-excludes-hnn-hyperlinearity: that records the amalgam form of the HNN group and its dichotomy with flexible stability; this isolates the operator-algebraic content of its hyperlinearity inside the base's matrix model and positions it against Popa's relative free-independence theorem.
  projective-trace-square-transfer-for-sl3-pair: that weakens the collapse to scalar commutators of every subgroup-central unitary; this weakens further, to the single amalgamated-free Haar unitary that an embedding of the HNN factor would supply.
  amenable-edge-hnn-preserves-hyperlinearity: that is the Brown--Dykema--Jung permanence for amenable edge groups; this explains the same permanence through Popa's theorem on centralisers of amenable subalgebras and locates the non-amenable edge as the whole content of the lane.
---

Let `C <= A` be a pair of countable groups, `G = <A, t | [t, C] = 1>
= A *_C (C x Z)` the HNN group of the lane, and write `B = L(C) subset
N = L(A)`, so that `L(G) = N *_B (B (x) L(Z))` is the tracial amalgamated
free product.  Let `iota : N -> M` be a trace-preserving embedding into a
tracial matrix ultraproduct `M`, and identify `N` with its image.

**Theorem.**  The following are equivalent.

1. `iota` extends to a trace-preserving embedding `L(G) -> M`.
2. There is a unitary `k in B' cap M` with `E_B(k^n) = 0` for all
   `n != 0` (so `W^*(B, k) = B (x) W^*(k)` and `k` is Haar) such that
   `N` and `W^*(B, k)` are free with amalgamation over `B`, i.e.
   `E_B(x_1 y_1 ... x_m y_m) = 0` whenever `x_i in N`, `y_i in W^*(B,k)`
   and `E_B(x_i) = E_B(y_i) = 0`.

Consequently `G` is hyperlinear iff `(2)` holds for SOME embedding `iota`
of `N` into some matrix ultraproduct, and `G` is the goal witness iff no
embedding of `N` admits such a `k`.

**Hierarchy of the lane's targets, for a fixed embedding `iota`.**

```text
(RCC)  B' cap M = N' cap M
  =>  projective transfer: every unitary of B' cap M has scalar commutators with u_h
  =>  no amalgamated-free Haar unitary in B' cap M          (= (2) fails).
```

Both implications are strict in content: a `k` as in `(2)` is a leak
(`[k, u_h]` has trace `0`, not `1`, by freeness), so `(RCC)` forbids it;
its commutator has trace `0` rather than modulus `1`, so projective
transfer forbids it; but `(2)` asks only for leaks with the full
amalgamated-free joint distribution.  The minimal statement the HNN lane
must prove is therefore: **no regular-trace matrix model of `A` carries a
Haar unitary in the `C`-centraliser that is free from `L(A)` with
amalgamation over `L(C)`.**

**Position against Popa's theorem.**  Popa (arXiv:1308.3982, *Independence
properties in subalgebras of ultraproduct II_1 factors*, main theorem)
proves: if `Q = B' cap M` is the centraliser of a separable AMENABLE
*-subalgebra `B` of a matrix ultraproduct `M`, then for every separable
subspace `X subset M (-) (Q' cap M)` there is a diffuse abelian von
Neumann subalgebra of `Q` free independent from `X`, relative to
`Q' cap M`.  This is the engine behind hyperlinearity permanence for
HNN extensions and amalgams over amenable edge groups
(`amenable-edge-hnn-preserves-hyperlinearity`, Brown--Dykema--Jung
Cor. 4.5): for amenable `C` the centraliser of `L(C)` in `R^omega` is
rich enough to contain the stable letter.  For the lane's pairs
`C = SL_n(Z)` the hypothesis fails exactly, and the theorem's conclusion
is what `(2)` asks for up to the difference between amalgamation over
`B` and over the bicommutant `Q' cap M`.  So the HNN lane asserts the
failure of relative free independence in the NON-amenable centraliser
`L(SL_n(Z))' cap R^omega` against `X = L(SL_n(Z[1/p]))`; the general
question whether amalgamated free products of Connes-embeddable algebras
over non-amenable subalgebras are Connes embeddable is open (Gao--Junge,
arXiv:2012.07940), and the lane is its first arithmetic instance.
