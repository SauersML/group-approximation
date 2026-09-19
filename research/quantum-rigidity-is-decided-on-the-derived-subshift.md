---
rg: 2
id: quantum-rigidity-is-decided-on-the-derived-subshift
kind: claim
title: Locally forced isolated points never affect quantum rigidity; a subshift is quantum rigid iff its derived subshift is, so a locally forced seed is rigid iff its seedless boundary is, and locally forced countable subshifts of finite Cantor–Bendixson rank are quantum rigid
distinct_from:
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that defines seeds and the class C, and proves rigidity of each construction by monotone chains; this proves once and for all that the seed orbit contributes nothing to rigidity, so only the seedless boundary needs an argument.
  quantum-rigidity-is-product-stable: that is closure under products; this is closure under adding or removing locally forced isolated orbits.
  free-rewritable-tape-layers-kill-finite-presentation: that shows a free, unconstrained layer destroys the finite presentation of the host; this shows a forced defect costs nothing.
  seeded-recursively-presented-groups-have-solvable-word-problem: that locates the word problem in the forcing from the origin; this shows that rigidity never looks at the origin.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-10, 2026-09-18; not independently reviewed). Route:
`quantum-rigidity-derived-subshift-proof`.

## Setting

`Λ` is finitely generated, with word metric `d` and balls `B_D`. `Y ⊆ A^Λ` is a subshift, with
`(g.x)(h) = x(g^(-1) h)`. `D`-quantum families (Q1–Q3) over a field `k`, and "`D`-quantum rigid over `k`", are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. `L_D(Y)` is the set of patterns on `B_D` that occur in `Y`.

- **Derived subshift.** `U ⊆ Y` is the set of isolated points of `Y`. It is open and invariant, so `Y' = Y ∖ U`
  is a subshift. Iterating gives `Y^(0) = Y`, `Y^(j+1) = (Y^(j))'`, the Cantor–Bendixson levels.
- **Local forcing.** An isolated point `x ∈ Y` is *locally forced with radius `ρ`* if there is a pattern `π` on
  `B_ρ` and `g ∈ Λ` with the following properties.
  - `π` isolates `x` at `g`: `x` is the only point of `Y` with `x(gf) = π(f)` for all `f ∈ B_ρ`.
  - The *forcing closure* is all of `Λ`. It is the increasing union of `F_0 = gB_ρ` and
    `F_(j+1) = F_j ∪ {h : h ∈ kB_ρ for some k such that every β ∈ L_ρ(Y) with β(f) = x(kf) whenever kf ∈ F_j has
    β(k^(-1)h) = x(h)}`.

  In words, the values of `x` can be deduced from `π` one site at a time, each deduction reading only the language
  of `Y` on one `ρ`-ball. Translates of a locally forced point are locally forced with the same radius.

## Theorem

Suppose every isolated point of `Y` is locally forced.
1. **Removing isolated points.** If `Y` is `D`-quantum rigid over `k`, so is `Y'`.
2. **Adding them back.** If `Y'` is `D`-quantum rigid over `k`, there is `D_1 = D_1(Y, D)` such that `Y` is
   `D'`-quantum rigid over `k` for every `D' ≥ D_1`.
3. **So `Y` is quantum rigid at all large scales iff `Y'` is.**

**Corollary A (seeds).** Let `(Y, π)` be an SFT compactification of `Λ` (conditions (C1), (C2) of
`tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`) with `y_*` locally forced.
- Then `U = Λ.y_*`: an isolated point of the closure of the dense orbit must lie in that orbit. Hence `Y' = ∂Y`.
- So `Y` is rigid iff the seedless boundary `∂Y` is rigid.
- Membership of `Λ` in `𝒞` through a locally forced seed is therefore decided entirely by `∂Y`, the SFT obtained
  from `Y` by forbidding the seed pattern.

**Corollary B (Cantor–Bendixson).** Suppose `Y^(n) = K` and, for each `j < n`, every isolated point of `Y^(j)` is
locally forced in `Y^(j)`.
- Then `Y` is quantum rigid at all large scales iff `K` is.
- In particular, if `Y` is countable with finite Cantor–Bendixson rank (`K = ∅`), then `Y` is quantum rigid over
  every field at all large scales. The empty subshift is rigid, since (Q1)–(Q3) force `W_0 = 0`.

**Corollary C (dimension one).** Over `Λ = Z`, every isolated point of an SFT is locally forced (route,
Section 5). The radius is the larger of an isolating radius and the longest forbidden word. So over `Z`, an SFT is rigid iff its derived subshift is.

## Calibration

- **`C_Z`** (`…++*−−…`, `+^Z`, `−^Z`).
  - `U` is the seed orbit, which Corollary C shows is locally forced.
  - `Y' = {+^Z, −^Z}` consists of two isolated points of `Y'`. Each is forced in `Y'`: a `+` forces its
    neighbours to be `+`.
  - `Y'' = ∅`.

  Corollary B gives rigidity of `C_Z` with no computation, recovering the monotone-chain proof in the parent.
- **Products.** `C_Z ⊠ C_Z` over `Z²` is countable, of Cantor–Bendixson rank 3: the orbit, then lines, then
  corners. Its levels are forced coordinatewise, so Corollary B applies (lane check).
- **Sharpness of part 1.** Rigidity cannot be created by isolated points either. Part 1 needs no forcing
  hypothesis, since a family for `Y'` is a family for `Y`.
- **Scope.** Local forcing is a hypothesis. An isolated point of a `Z²`-SFT forced only by a global compactness
  argument is not covered, and the route's forcing lemma fails without it.

## For the (SEED) gate (SYNTHESIS v6)

- **Rigidity lives at infinity.** For a locally forced seed, the forcing from the origin carries the whole word
  problem (`seeded-recursively-presented-groups-have-solvable-word-problem`). Rigidity never sees that forcing:
  it is a property of `∂Y` alone.
- **Scattered seeds are free.** A locally forced SFT compactification that is countable, of finite
  Cantor–Bendixson rank with forced levels, is automatically rigid. For such seeds, (SEED) and CAP lose their
  quantum condition. They become purely combinatorial: "does a locally forced scattered SFT compactification of an
  fp overgroup exist?", and "can its forcing cost be arbitrary?".
- **Where caps can come from.** Any cap on the word problem of rigid seeds must be imposed by rigidity of an
  uncountable perfect kernel (tree ends, boundaries of hyperbolic pieces), or by local forcing itself. It can never
  come from the origin.

## Lesson for general BH

**The origin is classical.** In every quantum family, the idempotent of a locally forced isolated point is central
and acts as the point evaluation.
- So defects, seeds, and any isolated orbit forced from its own pattern are invisible to quantum rigidity. They can
  be added or removed at will.
- With `free-rewritable-tape-layers-kill-finite-presentation`, this gives a clean division:
  - freedom in the perfect part of the space (unconstrained layers) is fatal;
  - structure at isolated points (forced defects, where the computation of a seed starts) is free.

  Minimality and rigidity must be paid for on the perfect kernel. The word problem is paid for at the origin.

## Referee (bh-ref-misc, 2026-09-18): PASS

Internal referee lane, not an external review. I checked the route
`quantum-rigidity-derived-subshift-proof` line by line.

- **Lemma F** (the induction along `F_j`).
  - The expansion of `Q` over the free sites of `kB_ρ` is valid by commutation, since the diameter is
    at most `2ρ ≤ 2D'`.
  - The `(Q3)` pruning at scale `ρ` is justified by monotonicity.
  - The absorption `E_c(h)T_β = T_β` for surviving `β` is exactly the forcing condition.
- **Lemma A.** `P_x` is central, so two isolating patterns give `P = PP' = P'P = P'`.
- **Lemma P**, by compactness.
- **Part 2.**
  - The certificate `[E_a(q), E_b(q')] ∈ I` holds because the universal algebra is a `D`-family for
    `Y'`. That uses that rigidity allows any `W_0`.
  - `Φ` and `Z` are finite, and `D_1` does not depend on `(q, q')`.
  - The key step is `P_β(w) = P_β(w)P_(x̂)`, because `wg_xB_(ρ_x) ⊆ wB_(D')`. It kills the `(Q3)`
    relators at `Φ` on `(1 − S)W_0`, and `(1 − S)W_0` is invariant.
- **Corollary C** (the gluing over `Z`). It needs `ρ = R ≥ m`, and that holds.
- **Scope.** Local forcing is read against the language `L_ρ(Y)`, not against local admissibility. The
  rule-based notion used in `seed-evaluation-is-bounded-by-the-forcing-radius` is stronger: it implies
  this one, but not conversely.

The companion node in the same commit, `seeded-recursively-presented-groups-have-solvable-word-problem`,
was read through part 3. Its `Π^0_1`-singleton search, the termination argument by König's lemma, and
the word-problem criterion are correct. PASS as far as read; part 4 was not checked.
