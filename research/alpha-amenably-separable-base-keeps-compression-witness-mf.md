---
rg: 2
id: alpha-amenably-separable-base-keeps-compression-witness-mf
kind: claim
title: A compression witness survives in an MF quotient whenever an alpha-invariant amenable quotient of the base separates gamma0 from alpha(Gamma), so F_2 with a->a^2, b->b^2 gives an MF, non-residually-finite compression wreath
distinct_from:
  multi-mover-collapse-criterion: that kills the witness b in every corona model when the base has property (T); this shows b survives in an MF quotient as soon as one alpha-invariant amenable quotient of the base separates gamma0 from alpha(Gamma), and that finite quotients always kill b whatever the base.
  a-t-menable-groups-have-no-rigid-compression-defect: that shows a-T-menable groups contain no rigid pair to feed the Kazhdan mechanism; this is about the compression wreath itself over a non-Kazhdan base, and gives a non-amenable, a-T-menable base where the wreath is actually MF with b alive.
  amenable-implies-operator-mf: that is the TWW input for amenable groups; this uses it on amenable quotients of a non-amenable wreath.
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that identifies a specific rope as a coset wreath over an a-T-menable base; this gives a separation criterion deciding when such coset wreaths keep the compression witness in MF models.
  relation-lamp-wreath-is-mf-with-nontrivial-fd-radical: that is a different lamp wreath with nontrivial finite-dimensional radical; here the finite-dimensional (finite-quotient) collapse of b coexists with a trivial MF radical.
  g-x-free-set-actions-sofic-when-kernel-amenably-separable: that uses amenable separability of a stabilizer kernel for action soficity; this uses alpha-invariant amenable separability of the compression images for MF-ness of the wreath.
artifacts:
  - research/alpha-amenably-separable-base-keeps-compression-witness-mf-proof.md
  - experiments/ptm-break-2026-09-17/separation_check.py
---

**ESTABLISHED.**

**Setting.** Let `Gamma` be a countable group and `alpha : Gamma -> Gamma` an
injective, non-surjective endomorphism. Let

- `V = <Gamma, t | t g t^-1 = alpha(g)>` be the ascending HNN extension,
- `X = V/Gamma`, and
- `W = K^(X) x| V`, where `K` is a countable abelian group (the literal
  family has `K = Z/2`).

Fix `gamma0 in Gamma \ alpha(Gamma)`. The compression witness is
`b = delta_{gamma0 t Gamma} - delta_{t Gamma}`, written additively in `K^(X)`
with a fixed `k != 0` in `K`. It is nontrivial, because
`t^-1 gamma0 t` is not in `Gamma`.

Let `N(Gamma, alpha)` be the set of normal subgroups `N` of `Gamma` with
`alpha^-1(N) = N` and `Gamma/N` amenable. This set is closed under finite
intersections.

**(A) Finite quotients always kill b.** For every base, `b` maps to 1 in every
finite quotient of `W`. In particular `W` is never residually finite.

**(B) One separation keeps b alive.** Suppose some `N` in `N(Gamma, alpha)`
has `gamma0 not in alpha(Gamma) N`. Then `W` has an amenable quotient in which
`b` survives. Hence `b` is not in `Rad_MF(W)`.

**(C) The criterion.** Suppose `{1}` and every `alpha^m(Gamma)`, `m >= 1`, are
`N`-closed, that is `H = intersection over N in N(Gamma, alpha) of H N`. Then
`W` is residually amenable, hence MF, and `Rad_MF(W) = 1`.

**(D) Example.** Take `Gamma = F_2 = <a, b>` with `alpha(a) = a^2` and
`alpha(b) = b^2`, and let `gamma0 = a`. The hypothesis of (C) holds with the
integral Magnus kernels `N_n = ker(F_2 -> (Z<<X,Y>>/deg >= n)^x)`, where
`a -> 1+X` and `b -> 1+Y`. These are alpha-invariant because `alpha` is
induced by `X -> 2X + X^2` and `Y -> 2Y + Y^2`. So

`W = (Z/2)^(V/F_2) x| <a, b, t | t a t^-1 = a^2, t b t^-1 = b^2>`

has these properties:

- it is finitely generated;
- it contains `F_2`, so it is non-amenable;
- it is residually solvable;
- it is not residually finite, and `b` dies in every finite quotient;
- it is MF, and `b` survives in some amenable quotient.

**(E) Necessity side.** If every amenable quotient `Gamma/N` with
`alpha^-1(N) = N` is finite, then `alpha(Gamma) N = Gamma` for all `N` in
`N(Gamma, alpha)`, and (B) and (C) are unavailable. Examples are finitely
generated Kazhdan groups, which have only finite amenable quotients, and
non-amenable simple groups. This matches Eckhardt's (T) collapse.

## Obstruction this certifies

The invariant is the `N(Gamma, alpha)`-closure of `alpha(Gamma)`:

`cl(alpha(Gamma)) = intersection over N in N(Gamma, alpha) of alpha(Gamma) N`.

Any proof that the compression witness `b` lies in `Rad_MF(W)` needs `gamma0`
to lie in this closure. If `gamma0` is outside it, (B) exhibits an MF model
through an amenable quotient that keeps `b` alive.

The Kazhdan route gets this for free: for a finitely generated (T) base every
`N` in the family has finite index, and then `alpha(Gamma) N = Gamma`. A
T-free replacement of the Kazhdan base in the compression core must therefore
choose a non-co-Hopfian base with `gamma0` in this closure. It is not enough
for the base to be any of the following:

- non-amenable, a-T-menable or Haagerup;
- residually finite, LERF, or finitely presented;
- such that the whole wreath `W` is non-residually-finite.

`F_2` with the squaring map has all of these properties and still gives an MF
wreath.
