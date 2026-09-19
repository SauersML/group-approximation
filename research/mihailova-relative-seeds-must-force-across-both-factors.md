---
rg: 2
id: mihailova-relative-seeds-must-force-across-both-factors
kind: claim
title: The rows of any configuration on F×F with a Mihailova stabilizer have infinitely generated stabilizers, so no SFT over one factor forces a row; diagonals, by contrast, are seeded row by row, for F×F always and for Q×Q whenever right multiplication acts on a rigid seed of Q by cellular automata
distinct_from:
  relative-seeds-descend-to-quotients-and-consume-membership: that descends a Mihailova relative seed on F_2×F_2 to the diagonal of Q×Q and reads its point as a two-sided colouring of Q; this works upstairs on F×F, where it shows that the forcing can never be done inside one factor, and it supplies the first two-sided seeds (diagonals seeded row by row).
  relative-seeds-on-free-groups-have-fg-stabilizers: that says forced points over a free group have finitely generated stabilizers; this applies it to the rows of a two-factor seed, whose row stabilizers must have normal core ker(F -> Q).
  deterministic-extensions-of-rigid-sfts-are-rigid: that transports a finite fibre over a rigid base along generating directions; here a whole row is transported along the second factor by a cellular automaton, and rigidity comes from the first row alone.
---

**ESTABLISHED** (lane bh-g3-topfree, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed). The Karrass–Solitar/Greenberg theorem is recalled, not re-read.

## Setting

- `F` is free on a finite basis `S`, `π : F -> Q` is onto, and `N = ker π`.
- `M(Q) = {(a, b) ∈ F × F : π(a) = π(b)}`. Membership in `M(Q)` is the word problem of `Q`.
- The action is `(η·y)(γ) = y(η^(-1)γ)`. The **row** of `y` at `v` is `r_v(u) = y(u, v)`, a configuration
  on the first factor. Columns are defined symmetrically.
- Quantum families and (L0) are as in `relative-seeds-glue-graphs-of-groups-proof` §2.

## Statement

1. **Row structure.** Let `y` be any configuration on `F × F`, over any alphabet, with `Stab(y) = M(Q)`.
   Then `r_v = v·r_1` for every `v`, and `H = Stab_F(r_1)` has normal core exactly `N`. The same holds
   for columns.
2. **Rows are never forced by their own factor.** Suppose `N ≠ 1` and `Q` is infinite. Then:
   - `H` is infinitely generated;
   - no row and no column of `y` is an isolated point of any SFT over `F`.
   So every relative seed for `(F × F, M(Q))` has to force each row through the other factor. That
   includes every Mihailova subgroup with an infinite, non-free quotient, e.g. every `Q` with
   hard word problem.
3. **Diagonals are seeded row by row.** Let `Q` carry a rigid seed: an SFT `Y_Q` with `(RS1)–(RS3)`
   of `relative-seeds-glue-graphs-of-groups-into-class-c` at a point `z_*` with trivial stabilizer.
   Suppose that for each `s ∈ S^(±1)` there is a sliding block code `Φ_s : Y_Q -> Y_Q` with
   `Φ_s(g·z_*) = gs·z_*` for all `g ∈ Q`, i.e. **right multiplication acts on the seed by cellular
   automata**. Then `(Q × Q, Δ_Q)` has a rigid relative seed whose rows are translates of `z_*`.
4. **Instances.**
   - `Q = F`: here `M(F) = Δ_F`, and the sink-moving automaton on the tree seed satisfies 3. So
     `(F × F, Δ_F)` has a rigid relative seed.
   - `Q = Z^n`: here `Φ_s` is the translation `x ↦ s·x`, so 3 applies to the product seed. It gives a
     relative seed for `Δ`, as corollary (b) of `relative-seeds-glue-graphs-of-groups-into-class-c` does
     for every subgroup of `Z^(2n)`.

## Proofs

**1.**
- `Δ_F ≤ M(Q)` gives `y(a^(-1)u, a^(-1)v) = y(u, v)`. With `a = v`, `y(u, v) = r_1(v^(-1)u)`, so
  `r_v = v·r_1`.
- Then `(a,b)·y = y` iff `r_1(v^(-1) b a^(-1) v x) = r_1(x)` for all `v, x`. That is,
  `v^(-1) b a^(-1) v ∈ H` for all `v`, i.e. `ba^(-1) ∈ core(H)`.
- `M(Q) = {(a, b) : ba^(-1) ∈ N}`. Comparing at `a = 1` gives `core(H) = N`.

**2.**
- `H ⊇ N ≠ 1`, and `N` is normal in `F`. A finitely generated subgroup of a free group that contains a
  nontrivial normal subgroup has finite index (Karrass–Solitar, Greenberg).
- So if `H` were finitely generated, `core(H) = N` would have finite index, and `Q` would be finite.
- An isolated point of an SFT over `F` has a finitely generated stabilizer, by item 3 of
  `sft-isolated-points-are-finite-state-across-finite-edge-groups` (or by
  `relative-seeds-on-free-groups-have-fg-stabilizers`). Every row `v·r_1` has the infinitely generated
  stabilizer `vHv^(-1)`.

**3.**
- **The SFT.** `Y` is the set of `y` on `Q × Q` with:
  - every row in `Y_Q`, by the rules of `Y_Q` along first-factor edges;
  - `r_(vs) = Φ_s(r_v)` for `s ∈ S^(±1)`, a rule on windows `(u B_ρ × {v}) ∪ {(u, vs)}`, where `ρ` is
    the radius of the `Φ_s`.
- **Well defined.** On the dense orbit `Q·z_*`, the `Φ_s` compose to right multiplication. So
  `Φ_(s^(-1)) = Φ_s^(-1)`, and `Φ_r = id` for every relator `r` of `Q`, by continuity. The `Φ_s` commute
  with the left shift. Hence `y ↦ r_1` is a bijection `Y -> Y_Q`, with inverse `x ↦ (r_v = Φ_v(x))`.
- **The action.** Under this bijection `(a, b)` acts on `Y_Q` by `x ↦ a·Φ_(b^(-1))(x)`.
- **(RS1)–(RS2).**
  - `y_*` corresponds to `z_*`, so it is isolated through the seed pattern of `z_*` in row `1`.
  - Its orbit corresponds to `{ab^(-1)·z_*}` = `Q·z_*`, which is dense in `Y_Q`.
  - `Stab(y_*) = {(a, b) : ab^(-1)·z_* = z_*} = Δ_Q`.
- **(RS3).** Let `(E)` be a `D`-family for `Y`, with `D ≥` the rigidity scale of `Y_Q` and `≥ ρ + 1`.
  - Row `1`'s idempotents form a `D`-family for `Y_Q`. For Q3, a pattern on a `D`-ball of row `1` that
    does not occur in `Y_Q` does not occur in `Y`, so its product vanishes by (L0). Hence they commute.
  - Transport. By (L0) and Q1, `E_ℓ(u, vs) = Σ_P E_P` over the patterns `P` on `u B_ρ × {v}` with
    `φ_s(P) = ℓ`, where `E_P` is the product of the site idempotents of `P`. The factors commute (Q2).
  - By induction on `|v|`, every idempotent lies in the commutative algebra generated by row `1`. So
    `(E)` commutes.

**4.**
- **The tree seed.** Let `Y_F` be the tree seed on `F`, with letters `S^(±1) ∪ {∗}` and the rule that
  exactly one of `x(u) = s`, `x(us) = s^(-1)` holds on each edge. Its points are the pointer fields
  toward a vertex (`∗` there) or toward an end.
- **It is a rigid seed.** It is the glued SFT of `relative-seeds-glue-graphs-of-groups-into-class-c` for
  the rose with trivial vertex and edge groups, so it is a rigid seed.
- **The automaton.** `Φ_s(x)(u)` is:
  - `s` if `x(u) = ∗`;
  - `∗` if `x(u) = s^(-1)` and `x(us^(-1)) = ∗`;
  - `x(u)` otherwise.

  It moves the sink from `g` to `gs` and fixes the end fields. So `Φ_s(g·z_*) = gs·z_*`.
- **The seed.** The resulting point is `y_*(u, v)` = the first letter of `u^(-1)v`, or `∗` if `u = v`.
- **`Z^n`.** Here `gs = sg`, so `Φ_s(x) = s·x`.

## Lesson for general BH

**Mihailova cannot be seeded one factor at a time.** A free factor forces only finitely generated
stabilizers. But the row stabilizers of any configuration with stabilizer `M(Q)` have normal core
`N = ker(F -> Q)`, which is infinitely generated whenever `Q` is infinite and not free. So the relators'
normal closure must be forced diagonally, across both factors. That is the precise form of "rules see
relators, not their conjugates".

**The diagonal is different.** Descended to `Q × Q` (bh-free-56), it is seeded row by row as soon as
right multiplication acts on a rigid seed of `Q` by cellular automata, as for free and free abelian
groups. That design contains a seed of `Q`, so it can never beat CAP for `Q`.

**So the Mihailova rung is a shortcut only through genuinely two-dimensional forcing on `F × F`.** Upstairs,
no row can be forced by its own factor (item 2). Downstairs, a row-forced design needs rows that are
isolated points of `Q`-SFTs with core-free stabilizers, and the design of item 3 is a seed of `Q`. The open question is
whether two-dimensional forcing can do what neither factor can.
