---
rg: 2
id: renormalizable-thompson-elements-give-baumslag-solitar
kind: claim
title: An element of kV with a bounded-prefix height-m tower renormalization gives BS(1,m) inside (k+1)V
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that is the open existence question for BS(1,2) in some nV; this is a sufficient criterion that turns it into a search for one renormalizable element of a lower-dimensional kV.
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that gives necessary conditions on a witness; this gives a sufficient construction of one.
  three-v-contains-aperiodic-rationals: that gives a periodic-point-free copy of Q in 3V; this criterion is the missing conjugacy step for such a copy's generator.
---

**ESTABLISHED** through `renormalizable-thompson-elements-give-baumslag-solitar-proof`.
Elementary lane proof; not independently reviewed. It generalizes the odometer and
baker-map computation of Attempt 1 in `bs12-embeds-in-brin-thompson-2v`, which fails
there only because the odometer is not in `V`. No priority claimed.

**Definition.** Let `k >= 1`, `m >= 2`, and `T ∈ kV`, acting on `X = C^k`. A
**height-`m` renormalization** of `T` is a pair `(A, φ)` with the following
properties.
1. `A ⊆ X` is clopen, `X = A ⊔ T A ⊔ … ⊔ T^{m-1} A`, and `T^m A = A`.
2. `φ: A -> X` is a homeomorphism with `φ ∘ T^m|_A = T ∘ φ`.
3. `φ` is **brick-local**: there is a finite partition of `A` into bricks `B_i` such
   that `φ` maps each `B_i` onto a brick `B'_i` by a prefix replacement
   `(u_{i,1} w_1, …, u_{i,k} w_k) ↦ (v_{i,1} w_1, …, v_{i,k} w_k)`.

**Statement.** If `T` has infinite order and a height-`m` renormalization, then
`s = T × id ∈ (k+1)V` and some `u ∈ (k+1)V` satisfy `u s u^-1 = s^m`. So
`BS(1,m) ≅ ⟨s, u⟩ <= (k+1)V`.

**Model.** The binary odometer `τ` on `C` has the height-2 renormalization
`A = C(0)`, `φ(0w) = w`, since `τ^2(0w) = 0 τ(w)`. It fails only because `τ ∉ V`.
So the criterion asks for an **odometer-like element that already lies in a
Brin–Thompson group**. Such an element must have no periodic point of nonzero exponent,
and logarithmic exponents and table lengths
(`bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`,
`bs12-images-in-nv-have-logarithmic-table-length`). Minimal substitutive reversible
machines such as SMART (`three-v-contains-aperiodic-rationals`) are candidates of the
right kind; none has been checked.

**Use for the rational stepping stones.** `aff-q-embeds-in-fp-simple-group` needs, for
every prime `p`, an element conjugate to its `p`-th power, inside one copy of `Q`. The
criterion supplies each `BS(1,p)` from height-`p` renormalizations of a single `T`.
Compatibility across primes, and with the roots of `T × id`, is not addressed.
