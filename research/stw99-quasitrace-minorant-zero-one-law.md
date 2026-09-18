---
rg: 2
id: stw99-quasitrace-minorant-zero-one-law
kind: claim
title: The linear-minorant mass of a II_1 AW*-factor dimension function is 0 or 1, and it is 1 exactly for W*-factors
distinct_from:
  stw01-quasitrace-crux-is-awstar-factor-w-star: that reformulates Problem I through large W*-corners or faithful CAP states; this produces CAP states by Hahn-Banach from any positive linear minorant of the dimension function, however small its mass, and proves the minorant mass is 0 or 1.
  stw01-kaplansky-2q-pedersen-retract-equivalence: that gives four equivalents of Problem I; this is a dichotomy inside a single II_1 AW*-factor and turns W*-ness into a finite weighted-cover inequality with arbitrary positive constant.
  stw01-full-free-group-algebra-quasitraces-are-traces: its certificates artifact (Proposition 4.1) shows exact subadditivity or superadditivity (constant 1) is the whole problem; this shows C-subadditivity for any constant C, or a Jensen inequality for pinchings with any constant, already forces W*-ness.
artifacts:
  - research/artifacts/stw99-quasitrace-minorant-zero-one-law-2026-09-17.md
---

**ESTABLISHED 2026-09-17 (proposed; referee requested)** by
`stw99-quasitrace-minorant-zero-one-law-proof`.

Let `M` be a type `II_1` AW*-factor, `tau` its normalized quasitrace and `D` its
dimension function. Put

```text
S_M(1) = inf { sum c_i D(p_i) : c_i >= 0, p_i projections (finitely many), sum c_i p_i >= 1 }.
```

**Theorem.** `S_M(1) ∈ {0, 1}`. The following are equivalent:

1. `M` is W*;
2. some nonzero positive linear functional `phi` satisfies `phi(p) <= D(p)` on
   projections;
3. `S_M(1) > 0`;
4. `tau(a_1 + ... + a_N) <= C sum tau(a_j)` for one constant `C` and all finite
   families in `M_+`;
5. `tau_N(G) <= C tau_N(E_N G)` for one constant `C`, all `N`, and all
   `G in M_N(M)_+`, where `E_N` is the diagonal pinching.

**Proof idea.**

- `S` is sublinear on `M_sa`. Hahn–Banach gives a positive `phi <= S` with
  `phi(1) = S(1)`.
- `phi <= D` on projections, and complete additivity of `D` make `phi` CAP.
- Unitary conjugates of `phi` separate projections: `m` conjugates of a
  projection of dimension `1/m` sum to `1`.
- Gow Cor. 3.10 then makes `M` W*. For W*-factors every cover has mass `>= 1`.

**Consequences** (artifact §3):

- Problem I ⟺ every normalized quasitrace on a unital C*-algebra dominates a
  nonzero positive functional ⟺ every quasitrace is C-subadditive for some `C`.
- In a counterexample factor, for every `eps`, there are projection covers of mass
  `< eps`. They need more than `1/eps` terms and more than `1/eps` pairwise
  noncommuting classes.
- Pinching can shrink `tau_N` by an arbitrary factor in a counterexample and by
  none in a W*-factor.

This is the noncommutative Maharam dichotomy. A counterexample's `D` would be a
pathological, completely additive, unitarily invariant measure on the projection
lattice, and pathology cannot be partial.

## Attempts

- *Noncommutative Kalton–Roberts* (non-pathology from uniform exhaustivity).
  Dies at the Gleason/Yeadon extension step for `II_1` lattices, which uses a
  normal trace.
- *Uniform Roe domination* `T <= K_R E(T)`. `K_R` is unbounded in the propagation
  `R`, so it gives no dimension-free constant.
