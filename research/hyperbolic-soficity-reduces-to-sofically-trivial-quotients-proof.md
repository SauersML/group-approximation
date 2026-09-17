---
rg: 2
id: hyperbolic-soficity-reduces-to-sofically-trivial-quotients-proof
kind: route
title: Make the sofic radical of a free product with the host surject onto an Olshanskii quotient
target: hyperbolic-soficity-reduces-to-sofically-trivial-quotients
requires:
  - sofically-trivial-iff-positive-permutation-cheeger
  - olshanskii-g-subgroup-quotient-theorem
---

Notation is that of the claim. `Rad(H)` is the sofic radical: the intersection
of the kernels of all homomorphisms from `H` into sofic groups. So `H` is
sofically trivial iff `Rad(H) = H`.

## Two formal facts

- **(F1) Functoriality.** If `phi : H -> K` is a homomorphism, then
  `phi(Rad(H)) <= Rad(K)`. Indeed, for every `psi : K -> S` with `S` sofic,
  `psi . phi` kills `Rad(H)`. In particular, for a subgroup `G <= H`,
  `Rad(G) <= Rad(H)`.
- **(F2) Detection.** A countable group `G` is sofic iff `Rad(G) = 1`. This is
  (I2) in `sofically-trivial-iff-positive-permutation-cheeger-proof`.

## Standard facts about hyperbolic groups used

- (H1) Free products of two hyperbolic groups are hyperbolic.
- (H2) A hyperbolic group has no infinite torsion subgroup. An infinite
  subgroup either is virtually cyclic, with limit set `{g^+, g^-}` for an
  infinite-order element `g`, or it is non-elementary.
- (H3) `E(X)`, for a non-elementary subgroup `X`, is the unique maximal
  finite subgroup normalized by `X` (Olshanskii's Proposition 1, as quoted in
  `olshanskii-g-subgroup-quotient-citation`).

## (1) => (5)

Let `G` be a nonsofic hyperbolic group, and let `M subset T` be finite.

**The free product.** Put `L = G * T`. By (H1), `L` is hyperbolic, and it is
non-elementary because it contains `T`.

**`E(L) = 1` and `E_L(T) = 1`.** Let `F <= L` be finite and normalized by `T`.
By Kurosh, `F <= u A u^-1` for a free factor `A` and some `u in L`.
- If some `x in T` has `w = u^-1 x u notin A`, then
  `u^-1 F u <= A cap w A w^-1 = 1`, since free factors are malnormal.
- Otherwise `u^-1 T u <= A`. Distinct conjugates of free factors meet
  trivially and `T != 1`, so `A = T` and `u in T`. Then `F <= T` is normalized
  by `T`, so `F <= E(T) = 1`.

So `E_L(T) = 1`. Since `E(L)` is normalized by `T`, also `E(L) = 1`. This is
the argument of `nonsofic-hyperbolic-question-reduces-to-one-fixed-host-proof`
with one factor fewer.

**The radical `R = Rad(L)`.**
- *Nontrivial.* By (F2), `Rad(G) != 1`, and by (F1), `Rad(G) <= R`.
- *Normal.* It is an intersection of kernels.
- *Infinite.* A finite normal subgroup of `L` lies in `E(L) = 1`.
- *Non-elementary.* By (H2), otherwise `R` is infinite virtually cyclic with
  limit set `{g^+, g^-}`. Since `R` is normal, `L` preserves this limit set, so
  `L <= Stab_L{g^+, g^-} = E(g)` is elementary, a contradiction.
- *`E(R) = 1`.* For `l in L`, the subgroup `l E(R) l^-1` is finite and
  normalized by `l R l^-1 = R`. By (H3) it lies in `E(R)`. So `E(R)` is a
  finite subgroup normalized by `L`, and `E(R) <= E(L) = 1`.

**G-subgroups.** For `X = T` and `X = R` we have `E(X) = 1 = E(L)`. So
`K(X) = X` and `K(L) = L`, and both indices equal `1`. By clause 1 of
`olshanskii-g-subgroup-quotient-theorem`, `T` and `R` are G-subgroups of `L`.

*A finitely generated substitute.* If one wants to apply the theorem only to
finitely generated subgroups, replace `R` by `R_0 <= R`, as follows.
- Pick independent infinite-order `x_1, x_2 in R`. Then
  `E(x_1) cap E(x_2)` is finite.
- `E(R) = cap E(x)` over the infinite-order `x in R` is an intersection of
  subgroups of a finite group. So finitely many `x_1, ..., x_m` already give
  `cap_i E(x_i) = E(R) = 1`.
- `R_0 = <x_1, ..., x_m>` is non-elementary with `E(R_0) <= cap_i E(x_i) = 1`.
- A homomorphism with `phi(R_0) = Q` has `phi(R) = Q`.

**The quotient.** Clause 2 of `olshanskii-g-subgroup-quotient-theorem` gives an
epimorphism `phi : L -> Q` onto a non-elementary hyperbolic group. It is
injective on `M` and satisfies `phi(T) = phi(R) = Q`. Then:

```text
Rad(Q) >= phi(Rad(L)) = phi(R) = Q          by (F1).
```

So `Q` is sofically trivial. Put `pi = phi|_T`. It is onto `Q` and injective on
`M`. `QED`

The bad group `G` is used only through `Rad(G) != 1`. Its ball does not need
to survive in `Q`, and it does not survive in any useful sense: `phi(G)` lies
in the sofically trivial group `Q`, but it may have sofic quotients of its own.

## (5) => (6) => (2) => (1)

- (5) => (6): take `M` empty. `Q` is non-elementary, hence nontrivial.
- (6) => (2): immediate.
- (2) => (1): a nontrivial sofically trivial group is not sofic, since the
  identity map would be a nontrivial homomorphism into a sofic group.

## (2) <=> (3) <=> (4)

Hyperbolic groups are finitely presented. Each of (2), (3) and (4) is about a
nontrivial hyperbolic group. The nontriviality matters in (3), because the
trivial group `<s | s>` has `h = 1`. For a nontrivial hyperbolic group, apply
Theorem B of `sofically-trivial-iff-positive-permutation-cheeger`:
(2) <=> (3) is (a) <=> (b), and (2) <=> (4) is (a) <=> (c) <=> (d).

## Kazhdan host

A torsion-free infinite group has `E = 1`, so (5) applies to a torsion-free
Kazhdan hyperbolic `T`. Quotients of Kazhdan groups are Kazhdan. Finite,
amenable and LEF groups are sofic, so a sofically trivial group has none of
them as nontrivial quotients. Applying (5) to the balls `M = B_n(T)` gives the
marked limit. Strict stability and the linear rate come from Theorem B (c) and
its rate.

## Hyperlinear version

Replace `Rad` by the hyperlinear radical, the intersection of the kernels into
hyperlinear groups. (F1) is formal. (F2) needs that `G / Rad_hyp(G)` is
hyperlinear. This follows as in (I2): finitely many detecting homomorphisms,
their product into a finite direct product of hyperlinear groups (which is
hyperlinear), and locality (`local-approximation-properties-are-marked-closed`).
The rest of the proof is unchanged.
