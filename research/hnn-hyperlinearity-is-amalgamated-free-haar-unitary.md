---
rg: 2
id: hnn-hyperlinearity-is-amalgamated-free-haar-unitary
kind: claim
title: The co-dense HNN group is hyperlinear iff some matrix model of the base carries a Haar unitary in the subgroup centraliser that is free from the base with amalgamation over the subgroup factor
distinct_from:
  hnn-route-is-relative-commutant-collapse: that proves commutant collapse sufficient for HNN nonhyperlinearity; this characterizes extension of a supplied actor embedding by an amalgamated-free Haar unitary. For maximal subgroups the two global exclusions are equivalent, although the constructions change the embedding.
  sl2-half-stability-excludes-hnn-hyperlinearity: that records the amalgam form of the HNN group and its dichotomy with flexible stability; this isolates the operator-algebraic content of its hyperlinearity inside the base's matrix model and positions it against Popa's relative free-independence theorem.
  projective-trace-square-transfer-for-sl3-pair: that is a finite-matrix estimate for arbitrary arithmetic assignments; this specifies the full HNN distribution in one actor model. Arithmetic maximality and the perfect-pair transfer theorem make their global exclusions equivalent.
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
   `E_B(z_1 z_2 ... z_m) = 0` for every alternating word -- consecutive
   letters taken from different algebras among `N` and `W^*(B, k)`, of
   any length `m >= 1` and starting from either algebra -- whose letters
   all satisfy `E_B(z_j) = 0`.  (An earlier version displayed only the
   even-length pattern `x_1 y_1 ... x_m y_m`; adjoints recover the
   pattern `y x ... y x` but not the odd-length ones, so the standard
   four-pattern formulation is the one meant and used; corrected after
   the 2026-08-21 audit.)

Consequently `G` is hyperlinear iff `(2)` holds for SOME embedding `iota`
of `N` into some matrix ultraproduct, and `G` is the goal witness iff no
embedding of `N` admits such a `k`.

**Hierarchy of the lane's targets, for a fixed embedding `iota`.**

```text
(RCC)  B' cap M = N' cap M
  =>  projective transfer: every unitary of B' cap M has scalar commutators with u_h
  =>  no amalgamated-free Haar unitary in B' cap M          (= (2) fails).
```

These implications follow from the required moment pattern: a `k` as in `(2)` is a leak
(`[k, u_h]` has trace `0`, not `1`, by freeness), so `(RCC)` forbids it;
its commutator has trace `0` rather than modulus `1`, so projective
transfer forbids it; but `(2)` asks only for leaks with the full
amalgamated-free joint distribution. This does not prove that either
implication is strict for the arithmetic pair. The exact statement the HNN lane
must prove is therefore: **no regular-trace matrix model of `A` carries a
Haar unitary in the `C`-centraliser that is free from `L(A)` with
amalgamation over `L(C)`.**

The fixed-embedding distinction does not imply a distinction between
the global exclusions. If `C` is a maximal proper subgroup of `A`,
`maximal-subgroup-hnn-equals-commutant-collapse` proves that HNN
nonhyperlinearity is equivalent to collapse in every canonical actor
embedding: a subgroup-central projection leak has stabilizer exactly
`C`, and tensor extraction produces a new canonical HNN model. This
applies to every `SL_n(Z)<=SL_n(Z[1/p])`, `n>=2`, by
`arithmetic-hnn-nonhyperlinearity-equals-global-collapse`. For an
arbitrary nonmaximal subgroup, a leak instead produces a relatively
embeddable proper overgroup of `C`; its stabilizer need not equal `C`.
The general statement is the commutant-separation closure in
`relative-embedding-is-commutant-separation`.

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

**The ordinary coset wreath has a different fixed-model pattern.**
The coset-Bernoulli wreath `W = (Z/2) wr_(A/C) A` of
`coset-bernoulli-ce-refutes-relative-commutant-collapse` has
`L(W) = L^infinity({+-1}^(A/C)) rtimes A`, so an embedding `iota` extends
to `L(W)` iff `M` contains commuting involutions `v_x`, `x in A/C`, with
`u_a v_x u_a^* = v_(ax)`, jointly Bernoulli (independent, trace `0`), and
`tau(f(v) u_a) = 0` for `a != e`. The distinguished leak is the
involution `v_C`, whereas the HNN construction supplies a Haar stable
letter. No description of the entire relative commutant follows from
these distinguished elements. In particular, for commensurated
arithmetic `C`, its orbits on `A/C` are finite, so an infinite-orbit
ergodicity argument cannot supply such a description. These fixed-model patterns differ,
but existence of their matrix models is equivalent by
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`. Tensor
averaging gives an HNN model from the ordinary lamps; a Gaussian tensor
limit gives ordinary lamps from the free binary model. The construction
changes the embedding and ambient ultraproduct. It does not place a free
Haar letter inside the original abelian carrier. The two candidate groups
have the same hyperlinearity status for every countable subgroup pair.

**1-bounded entropy cannot separate the two scenarios.**  If `k` as in
`(2)` exists, then `k` and `u_h k u_h^*` are `*`-free Haar unitaries (an
alternating word in `W^*(B,k) (-) B` and `N (-) B` has zero
`B`-expectation), both commuting with `L(C_0)`, `C_0 = C cap hCh^-1`;
so `L(C_0)' cap M_0` contains a free group factor, `M_0 = W^*(N, k) ~= L(G)`.
This is not an obstruction: for `C_0` with property (T), `L(C_0)` is
strongly 1-bounded (Jung), and Hayes' bound on the 1-bounded entropy of
the algebra generated by a diffuse subalgebra together with its
normaliser gives `h(L(C_0) (x) L(F_2) : M_0) <= h(L(C_0) : M_0) < infinity`
— a free group factor sitting in the centraliser of a strongly 1-bounded
algebra carries no entropy relative to the ambient algebra, exactly as
`L(F_2) subset L(C_0 x F_2)` does.  The entropy count listed among the
attempts of `relative-commutant-collapse-for-sl2-pair` therefore cannot
close `(2)`. Further information about the joint actor and auxiliary
element is required. For maximal subgroups this can also be supplied
through the equivalent global commutant-collapse formulation, without
keeping the same auxiliary distribution in intermediate models.

**Coordinatewise scope for Kazhdan subgroups.** When `C` has property
(T), conjugation by its genuine ultraproduct representation has a
spectral gap relative to its fixed vectors. This does not replace an
arbitrary approximate coordinate tuple for `C` by an exact
representation. Consequently it does not lift a subgroup-central
unitary to unitaries commuting exactly with those arbitrary tuples.

If exact coordinate representations `pi_n:C->U(d_n)` are separately
available, their uniform Kazhdan gap does let an asymptotically central
unitary be approximated by unitaries in the coordinate commutants:
project onto each commutant and take a polar unitary there. This
conditional coordinate conclusion concerns commutation only. The
required `B`-valued freeness remains the full limiting moment condition
in (2); it is not established by coordinate centralizer normalization.
The theorem above therefore uses neither arbitrary coordinate
exactification nor a finite-coordinate amalgamated-freeness assertion.
