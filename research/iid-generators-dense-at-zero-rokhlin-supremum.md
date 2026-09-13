---
rg: 2
id: iid-generators-dense-at-zero-rokhlin-supremum
kind: claim
title: At zero Rokhlin supremum, generating i.i.d. partitions of a Bernoulli shift are dense among i.i.d. partitions of the same distribution
distinct_from:
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks for one isomorphism between Bernoulli shifts of different base entropy at zero supremum; this is a genericity statement inside one Bernoulli shift, which gives those isomorphisms by the Baire category theorem.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that proves the same density fails on every nonamenable group with positive supremum; this asks for it at supremum zero, where that obstruction is empty.
  bernoulli-classes-meager-on-central-locally-finite-hosts: that concerns conjugacy classes in the space of actions; this concerns partitions inside one fixed Bernoulli shift.
---

**OPEN.** Let `G` be countably infinite with `h^Rok_sup(G) = 0`. Let `(K, κ)` and `(L, λ)` be finite bases
with `H(κ), H(λ) > 0`, and put `X = (K^G, κ^G)` with measure `µ`. Let `Ind_λ(X)` be the set of partitions
`ξ = {ξ_ℓ : ℓ ∈ L}` of `X` whose `G`-translates are independent with `µ(ξ_ℓ) = λ(ℓ)`, with metric
`d(ξ, ζ) = µ(ξ ≠ ζ)`. Then the generating partitions are dense in `Ind_λ(X)`.

**Payoff.** By route `zero-supremum-collapse-via-dense-iid-generators` and the Baire category theorem,
`K^G ≅ L^G` for all such bases with `Ind_λ(X)` non-empty. So all Bernoulli shifts of finite positive base
entropy over `G` would be isomorphic. That is the finite-entropy part of the strong form of
`zero-rokhlin-supremum-forces-bernoulli-collapse`. It would apply to the binary Leavitt unit group, Thompson's
`V` and the tester host as soon as their supremum is zero.

**Model tests.**
- Sofic and amenable groups have `s = ∞` and fail the hypothesis. There the conclusion is false for
  `H(λ) < H(κ)`: `Ind_λ(X)` is non-empty but contains no generating partition.
- On nonamenable groups with `s > 0` the density fails for every pair of bases
  (`iid-generators-not-dense-at-positive-rokhlin-supremum`). At `s = 0` the bound used there,
  `H(γ | 𝒜) >= h^Rok_G(X) − h^Rok_G(𝒜)`, is `>= 0` and says nothing.
- No group with `s = 0` is known, so the claim is not tested on an example.

## Attempts

- **Outer-entropy obstructions.** Empty at `s = 0`. Every free ergodic action has Rokhlin entropy `0`, so
  sub-additivity gives no lower bound on the distance from a generating partition to an i.i.d. partition.
- **Seward's perturbative factor theorem.** Not applicable. Theorem 9.2 of arXiv:1804.05269 returns a
  partition that is exactly Bernoulli over `Σ` near a given `ξ` only when `H(p̄) <= h^Rok_G(X | Σ)` and
  `h^Rok_(G,µ)(ξ | Σ)` is close to `H(p̄)`. At `s = 0` both force `p̄` to be trivial. Density needs an
  exactification step without entropy room: change an i.i.d. partition on a set of small measure so that it
  captures a prescribed finite partition and stays exactly i.i.d.
- **Predictable recodings capture nothing.** Let `ζ` be a process independent of `ξ` that also carries an
  invariant random order. Suppose `ξ'(g) = π_g(ξ(g))`, where `π_g` is a `λ`-preserving permutation of `L`,
  measurable in `ζ` and in `ξ` at sites earlier than `g`. Then `ξ'` is i.i.d. with law `λ` and independent of
  `ζ`.
  - Order a finite `F ⊆ G` by the random order.
  - Conditional on `ζ` and on `ξ` at the earlier sites, `ξ(g)` has law `λ`, so `ξ'(g)` has law `λ` and is
    independent of `ζ` and of `ξ'` at the earlier points of `F`.

  So the exact recodings that are easy to write down carry no information about the complement they would
  have to capture.
- **Krieger density.** Holds at `s = 0` (2026-09-13). Generating partitions are `d^Rok`-dense among all
  finite-entropy partitions of an ergodic action exactly when its Rokhlin entropy is `0`
  (`generators-dense-iff-zero-rokhlin-entropy`, from Seward's small-support generators). So every i.i.d.
  partition has generating partitions arbitrarily close to it, with the same window statistics up to any
  error, using two extra labels on a small set. The non-exact half of this claim is free, and the claim is
  purely an exactification statement.
- **Where it dies.** Exactness: no construction changes an exactly i.i.d. partition on a small set, keeps it
  exactly i.i.d., and increases the information it carries.
