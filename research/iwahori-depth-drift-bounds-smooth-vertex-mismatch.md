---
rg: 2
id: iwahori-depth-drift-bounds-smooth-vertex-mismatch
kind: claim
title: Depth drift gives a sharp uniform lower bound on the Iwahori mismatch of smooth q-adic vertex pairs
artifacts:
  - experiments/sl2-pq-iwahori-mismatch-2026-09-17/README.md
  - experiments/sl2-pq-iwahori-mismatch-2026-09-17/chartab.py
  - experiments/sl2-pq-iwahori-mismatch-2026-09-17/mismatch_lp.py
  - experiments/sl2-pq-iwahori-mismatch-2026-09-17/depth_drift.py
distinct_from:
  pure-dyadic-clifford-slots-have-a-uniform-one-third-gap: that is q = 2 only, bounds common rank by 2/3 plus a correction charged to all conductor-at-most-one mass, and is phrased for SL_2(Z/2^a) Iwahori restrictions of modular vertices; this holds for every prime q, charges only the K_0-trivial mass, is sharp at every level k >= 2, and is proved by one signed potential (depth drift) instead of Clifford slot bookkeeping.
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich Question 1.4 for exact representations of SL_2(Z) whose restrictions need not be smooth; this is a finite-group mismatch inequality for smooth representations of the two maximal compact subgroups of SL_2(Q_q).
  sl2-z-inverse-pq-is-flexibly-hs-stable: that is the global stability question for SL_2(Z[1/pq]); this is the local q-adic input that makes its exact vertex pairs repairable (sl2-pq-exact-vertex-pairs-have-uniform-linear-repair).
---

Let `q` be any prime and put `c = (q-1)/(q+1)`.

**Setting.**
- `K_0 = SL_2(Z_q)` and `K_1 = g K_0 g^(-1)`, where `g = diag(q,1)`.
- `I = K_0 ∩ K_1 = {b ≡ 0 mod q}` is an Iwahori subgroup.
- `σ_0` and `σ_1` are finite-dimensional continuous unitary representations of
  `K_0` and `K_1` on spaces of the same dimension `d`.
- `θ_i` is the fraction of the space of `σ_i` that is fixed by `K_i`.
- `ε = 1 - m/d`, where `m` is the largest dimension of an `I`-subrepresentation
  common to `σ_0|_I` and `σ_1|_I`.

**Theorem.**

```text
ε >= (1 - min(θ_0, θ_1)) (q-1)/(q+1).                    (DD1)
```

The same holds, with `θ_i` still the `K_i`-fixed fraction, for
representations of `K_0 × P` and `K_1 × P`, and a common subrepresentation of
`I × P`, where `P` is any compact group.

**Mechanism.** For an irreducible representation `τ` of `I`, define:
- `d_0(τ)` = least `a >= 1` with `τ` trivial on the principal congruence subgroup `K(q^a)`;
- `d_1(τ)` = the same with the conjugate `K_1(q^a) = g K(q^a) g^(-1)`;
- the depth drift `Φ(τ) = d_1(τ) - d_0(τ)`, which lies in `{-1, 0, 1}`.

Every nontrivial irreducible `ρ` of `K_0` satisfies

```text
E_(ρ|I) Φ - c · dim ρ^I / dim ρ >= c,                    (DD2)
```

where `E` averages over the `I`-constituents weighted by dimension. The
Atkin--Lehner element `[[0,q],[1,0]]` swaps `K_0` and `K_1` and reverses the
sign of `Φ`. Put `f = Φ` on nontrivial `τ` and `f = -c` on the trivial one.
Then `|f| <= 1`, and `E f >= (1-θ_0)c - θ_0 c` through `K_0` while
`E f <= -c` through `K_1`. Only the mismatched part can separate the two
averages, which gives `(DD1)`.

**Sharpness.** The bound is attained.
- Equality in `(DD2)` holds for the Steinberg representation, for every
  principal series, and for the two halves of the reducible principal series.
- The linear programme in `mismatch_lp.py` gives the exact least mismatch at
  level `k` equal to `(1-θ)c` for every `k >= 2` computed, namely `q = 2`,
  `k = 2, 3` and `q = 3`, `k = 2`, with `θ = 0` and `θ = 1/2`.
- `depth_drift.py` checks `(DD2)` and its `K_1` mirror in exact rationals for
  `(q,k) = (2,1..4), (3,1..2), (5,1)`.

**Consequence.** Any q-adic gluing of smooth vertex representations in which
a non-vanishing fraction of each vertex is K-nontrivial has an Iwahori
mismatch of at least a fixed constant: `c(1-θ) >= 1/6` when `θ <= 1/2`.
So smooth-vertex gluing cannot produce a sequence with `ε → 0` that keeps a
positive nontrivial q-adic fraction. Combined with (T;FD) of the edge group,
`sl2-pq-exact-vertex-pairs-have-uniform-linear-repair` turns this into
linear repair of every exact vertex pair of `SL_2(Z[1/pq])`.

Proof: `iwahori-depth-drift-bounds-smooth-vertex-mismatch-proof`.
