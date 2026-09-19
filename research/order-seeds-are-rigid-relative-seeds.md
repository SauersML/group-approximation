---
rg: 2
id: order-seeds-are-rigid-relative-seeds
kind: claim
title: If a finitely generated group acts order-preservingly on a linear order with a densely ordered orbit, a point whose stabilizer is finitely generated, and monotone paths between orbit points, then the cut at that point is a rigid relative seed; and it is the tool behind the finitely generated positive cone seeds (whose orders are always discrete; see finitely-generated-positive-cones-are-discrete)
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that builds relative seeds from tree splittings (pointers, Stallings cores, finite shifts); this builds them from an order on an orbit, with rigidity from monotone chains and no tree.
  baumslag-gersten-groups-lie-in-class-c: that seeds the stable letter of BS(1,n) by a line sink in the tree; this seeds it by the real cut of the affine action, as one instance of a general order construction.
  baumslag-gersten-seed-forcing-length-is-non-elementary: that uses the real-cut seed for (BS(1,2), ⟨b⟩); this isolates the general mechanism behind it.
---

**ESTABLISHED** (lane proof, bh-emitter-a, 2026-09-18; elementary; not reviewed). Relative seeds and `𝓡` are as
in `relative-seeds-glue-graphs-of-groups-into-class-c`. The configuration action is `(h.y)(g) = y(h^{-1}g)`.

## Statement

Let `A` be finitely generated, acting by order-preserving bijections on a linearly ordered set `(Ω, <)`. Let
`p ∈ Ω`, and put `O = A·p` and `C = Stab(p)`. Fix a finite symmetric generating set `S` of `A` such that
`S ∩ C` generates `C`. Assume:
- (D) `O` is densely ordered;
- (M) whenever `g·p < g′·p`, there is a path `g = g_0, g_1 = g_0 s_1, …, g_m = g′` with `s_i ∈ S` and
  `g_i·p ≤ g_(i+1)·p` for all `i`.

Then `(A, C) ∈ 𝓡`. The forced point is the cut `y_p(g) = cmp(g·p, p) ∈ {<, =, >}`, rigid for every `D ≥ 1` over
every field.

**The SFT.** For each `s ∈ S`, compare the letters at `g` and `gs`:
- if `s·p = p`, they are equal;
- if `s·p > p`, the pair lies in `{<<, <=, <>, =>, >>}`;
- if `s·p < p`, the reversed condition holds.

These rules are uniform in `g`, because `g` preserves order, so `gs·p > g·p` iff `s·p > p`. The seed is `=`
at `1`.

## Proof

- **(RS1).** Let `f ∈ Y` with `f(1) = '='`.
  - On `C`, `f` is `=`, by equality along the generators `S ∩ C`.
  - If `g·p > p`, take a monotone path from `1` to `g` given by (M). Equal steps preserve letters. After a
    strict step, `=` is followed only by `>`, and `>` only by `>`. So `f(g) = '>'`.
  - If `g·p < p`, read a monotone path from `g` to `1` backwards: only `<` can precede `=` or `<`. So
    `f(g) = '<'`.
  - Hence `f = y_p`. The translates are `(h.y_p)(g) = cmp(g·p, h·p)`, the cuts at orbit points, so
    `Stab(y_p) = C`.
- **(RS2).** Let `f ∈ Y`.
  - Equality along `S ∩ C` makes `f(g)` depend only on `g·p`.
  - Along the paths of (M), `f` is nondecreasing for `< ≺ = ≺ >`. After a strict step, `=` never recurs.
  - So `f` is a Dedekind cut of `O`, with at most one `=`.
  - A cut with `=` at `h·p` is `h.y_p`. By (D), any other cut, including the two constant ones, is a pointwise
    limit of cuts at orbit points approaching it. `O` has no endpoints, since `A` is transitive on it.
  - So `Y` is the orbit closure of `y_p`.
- **(RS3).** Let `E_ℓ(g)` be a `D`-family with `D ≥ 1`.
  - Exact transport along `S ∩ C` makes `E_ℓ` constant on `gC`.
  - Along a strict step `g → gs` there are orthogonality relations from the forbidden pairs, and commutation
    at distance 1. They give:
    - `E_>(g) ≤ E_>(gs)` and `E_<(gs) ≤ E_<(g)`;
    - `E_=(g) ≤ E_>(gs)` and `E_=(gs) ≤ E_<(g)`.
  - By transitivity along the paths of (M), for `g·p < g′·p`:
    - `E_>(g) ≤ E_>(g′)` and `E_<(g′) ≤ E_<(g)`;
    - `E_=(g) ≤ E_>(g′)` and `E_=(g′) ≤ E_<(g)`.
  - So the `E_>` form a chain and commute.
  - Each `E_=(g)` lies below, or is orthogonal to, every idempotent at a site with a different orbit point.
    For example, `E_=(g) E_<(g′) = E_=(g) E_>(g′) E_<(g′) = 0`.
  - On one orbit point, the idempotents are equal by transport.
  - Hence all site idempotents commute. `∎`

**Discrete orbits.** If `O` is discrete, as in `Z`, forbid `<>` along `s` whenever no orbit point lies strictly
between `p` and `s·p`. The same proof applies wherever every gap of `O` is crossed by a single step. `C_Z` is the
case `A = Z`.

## Instances

1. **`(BS(1,2), ⟨b⟩)`.** The action is the affine action on `R` with `p = 0`. `O = Z[1/2]` is dense, and (M)
   uses `b`-moves to a level `j` with `2^j | (r′ − r)` followed by `a`-steps. This is the real-cut seed `y_R` of
   `baumslag-gersten-seed-forcing-length-is-non-elementary`.
2. **Finitely generated positive cones.** Suppose `A` has a left order `≺` whose positive cone `P` is generated
   as a semigroup by `S⁺ = {s ∈ S : s ≻ 1}`.
   - **Correction (bh-emitter-a, 2026-09-19).** This instance was first stated for dense `≺`, which is vacuous: a
     finitely generated cone always makes `≺` discrete (`finitely-generated-positive-cones-are-discrete`). The
     real statement uses the "Discrete orbits" variant and is proved in
     `finitely-generated-positive-cones-give-rigid-seeds`. The referee's caveat below anticipated this.
   - Take `Ω = A`, `p = 1` and `C = 1`. Then (M) holds, because `g ≺ g′` means `g^{-1}g′ = s_1 ⋯ s_m` with
     `s_i ∈ S⁺`, and each step `g s_1 ⋯ s_i` increases.
   - So `A ∈ 𝒞`, and its forced point is the sign function of the order.
   - Examples: the Dubrovina–Dubrovin orders on braid groups have finitely generated positive cones, and they
     are discrete.
3. **Point stabilizers generally.** Any (M)-action with a finitely generated point stabilizer supplies a rigid
   relative seed for that stabilizer. So order actions are a source of relative seeds for subgroups that fix no
   tree vertex, which is the tool the seed tower asked for.

## What it certifies, and a CAP question

- **The oracle.** The forced point is the comparison oracle `g ↦ cmp(g·p, p)`. In instance 2 it is the positivity
  problem of `P`, which is decidable given `WP(A)`: positivity and negativity are both c.e.
- **The CAP relation.**
  - `WP(A) ≤ positivity ≤ Eval(y_*)`, so order seeds refute CAP only through groups with a hard word problem.
  - **Question (O).** Is there a finitely presented group with a left order whose positive cone is finitely
    generated (necessarily a discrete order), and whose word problem lies outside a given class, such as EXP?
  - A yes refutes CAP. Relatively, a monotone-connected order action with a hard point stabilizer would do the
    same along a Higman tower.

## Lesson for general BH

Relative seeds need not come from trees. Any order-preserving action with monotone connectivity gives one, and
rigidity is again just monotone chains.
- **What this changes.** It moves the seed tower's missing tool (relative seeds over distorted, tree-free
  subgroups) to a question about orders.
- **The CAP question.** A rigid seed then certifies exactly the comparison problem of the order. Whether CAP
  fails becomes: can a finitely generated positive cone, or a monotone-connected action, have a hard comparison
  problem?

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS

I checked the Statement and Proof line by line.

- **The rules.** They are uniform because `gs·p ≷ g·p` iff `s·p ≷ p`. `y_p` satisfies them.
  Conversely, every monotone cut of `O` with at most one `=` satisfies them, since `(=,=)` is excluded
  along strict steps.
- **(RS1).**
  - `=` spreads over `C` along `S ∩ C`.
  - Along a monotone (M)-path from `1`, equal steps are exactly steps by elements of `C`. After the
    first strict step only `>` is possible, and backwards only `<`.
  - So `f = y_p`, and `Stab(y_p) = C` (take `g = h` in `cmp(g·p, h·p)`).
- **(RS2).**
  - Points descend to `O` and are cuts with at most one `=`. A cut with `=` at `h·p` is `h.y_p`.
  - The remaining cuts are limits. I checked this with an enumeration of `O` and (D).
  - A gap `l < u` with nothing between cannot occur, by (D), and `O` has no endpoints, by
    transitivity.
- **(RS3).** The same four order relations as in the real-cut seed, and the same cross cases, give
  commutation for every `D ≥ 1`. Idempotents at `g` and `gc` (`c ∈ C`) are equal by transport.
- **Instance 1.** It reproduces `y_R` exactly, with `< ↔ +`, `= ↔ *`, `> ↔ −`. (M) holds via `b`-moves
  to a level where `2^j` divides `r′ − r`, then `a`-steps.
- **Instance 2.** (M) holds because `g ≺ g s_1 ⋯ s_i` increases for `s_i ≻ 1`. So a dense left order
  with a semigroup-generated positive cone gives `A ∈ 𝒞`.
- **Oracle.** Positivity is decidable from `WP(A)`: positive, negative and trivial elements are each
  c.e.

**Not checked.** Whether the Dubrovina–Dubrovin orders are dense (the node says it is recalled).
Orders with finitely generated positive cones are often discrete; in that case the "Discrete orbits"
variant must be used, and it needs every gap to be crossed by a single step.
