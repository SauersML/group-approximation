---
rg: 2
id: sl2-pq-exact-vertex-pairs-have-uniform-linear-repair
kind: claim
title: Exact vertex pairs of the q-adic amalgam of SL2(Z[1/pq]) glue to exact representations with linear cost
distinct_from:
  pure-dyadic-iwahori-pairs-have-uniform-linear-repair: that repairs exact pairs of SL_2(Z) vertex representations in the Dogon--Vigdorovich amalgam SL_2(Z[1/2]) = SL_2(Z) *_(Γ_0(2)) SL_2(Z), only in the pure-dyadic sector; this repairs every exact pair for the amalgam SL_2(Z[1/pq]) = SL_2(Z[1/p]) *_D SL_2(Z[1/p])^g, whose vertex groups have the congruence property and whose edge group has (T;FD).
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that is the odd-level sector of the same SL_2(Z) amalgam; this is the q-adic amalgam of SL_2(Z[1/pq]), with no sector restriction.
  iwahori-local-global-defect-question: that asks for this local-to-global modulus for SL_2(Z) *_(Γ_0(2)) SL_2(Z), where vertex representations are arbitrary; this proves it with a linear modulus one prime up, where every vertex representation is congruence.
---

Let `p ≠ q` be primes.
- `A = SL_2(Z[1/pq])`.
- `C = SL_2(Z[1/p])`.
- `C' = g C g^(-1)`, with `g = diag(q,1)`.
- `D = C ∩ C' = {γ ∈ C : γ_12 ≡ 0 mod q}`.

The Bruhat--Tits tree of `SL_2(Q_q)` gives

```text
A = C *_D C'.                                              (VR0)
```

Fix finite generating sets `S_C`, `S_(C')` and `S_D`, where `S_D` contains a
Kazhdan set of `D` for finite-dimensional representations, with constant
`κ > 0`. Put `c = (q-1)/(q+1)`.

**Theorem.** Let `σ_0 : C → U(W)` and `σ_1 : C' → U(W)` be exact unitary
representations on the same finite-dimensional space. Suppose that

```text
δ = max_(s ∈ S_D) ||σ_0(s) - σ_1(s)||_2       (normalized Hilbert--Schmidt).
```

Then there is an exact unitary representation `π : A → U(W)` of the same
dimension with

```text
max_(s ∈ S_C) ||π(s) - σ_0(s)||_2,  max_(s ∈ S_(C')) ||π(s) - σ_1(s)||_2  <=  K δ,
K = 8(1 + 4/(κ√c))/κ + 2/(κ√c).                         (VR1)
```

In fact `π` factors through `A → ∏_(ℓ ∤ pq) SL_2(Z_ℓ)`, so it is trivial on
the q-adic part.

**Meaning.**
- Every pair of exact vertex representations that almost agrees on the edge
  group is close to one exact representation of `A`, uniformly in the dimension
  and in the congruence levels.
- The q-adic place cannot be the source of an instability of `SL_2(Z[1/pq])`.
  By `iwahori-depth-drift-bounds-smooth-vertex-mismatch`, any nontrivial
  q-adic content costs a fixed fraction of the edge match, so almost-agreeing
  pairs are almost q-adically trivial.
- `sl2-pq-flexibility-from-sl2-p-flexibility` uses this to reduce
  `sl2-z-inverse-pq-is-flexibly-hs-stable` to flexible stability of the
  one-prime group `SL_2(Z[1/p])`.

Proof: `sl2-pq-exact-vertex-pairs-have-uniform-linear-repair-proof`.
