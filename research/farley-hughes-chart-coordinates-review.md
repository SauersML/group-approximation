---
rg: 2
id: farley-hughes-chart-coordinates-review
kind: claim
title: Referee review of 4c81e934b2 (FH certificates have prefix chart coordinates) — the chart lemma, prefix connectors and finite tables are correct at FH source and do absorb twisted connectors; the 2^O(n) orbit cap holds for nested (compact ultrametric) certificates once the address-length bound is proved by domain-tree depth, which the sketch omits; item 5 needs nesting and misstates the composition-factor claim; "dead for every certificate" should read "for every nested certificate"
distinct_from:
  farley-hughes-certificates-have-prefix-chart-coordinates: that is the lane node under review; this checks items 1–3 at source, repairs the complexity accounting of item 4(a), corrects item 5, and fixes the scope.
  generation-axiom-rover-door-review: that review left twisted connectors open; this confirms that finite chart coordinates close that door for nested certificates.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 4c81e934b2 by bh-gate1-abstract).**
The repairs in §§3–4 are the referee's; they are **not independently reviewed**.

Read at source in Farley–Hughes arXiv:2010.08035v1:
- Def. 3.12, Conv. 3.9, Cor. 3.8, Prop. 3.16, Cor. 3.20, Prop. 3.24;
- Def. 4.2, 4.7, 4.10, 4.12, 4.18, Remark 4.19, Prop. 4.20, 4.22, 4.24, Lemma 4.25, Cor. 4.26;
- Def. 6.1, 6.6, Thm 6.9, Ex. 4.35, Prop. 6.23, Ex. 8.4, Thm 8.2, Prop. 8.10.

## Verdicts

| item | verdict |
|---|---|
| hypotheses quoted, (E0) from 0-connectivity | **PASS** (Def. 6.6, Thm 8.2 and Prop. 8.10 verbatim) |
| 1. chart lemma | **PASS** |
| 2. prefix connectors | **PASS** |
| 3. finite tables and transition rules | **PASS** |
| twisted connectors absorbed (the door of 79ad158419) | **PASS**: this is the right fix |
| 4(a) orbit cap `2^(O(n))` | **PASS for nested certificates, with the length bound repaired**; the sketch as written is incomplete |
| 4(b) word problem exponential over `WP(H_τ)` | plausible sketch, not checked in detail |
| 5. structure groups | **needs Def. 3.12**; the composition-factor claim is **false as stated**, repaired below |
| scope "dead for every certificate" | **narrow to nested certificates** |

## 1–3. The chart construction is right at source

- **(E0).** By Def. 6.6, 0-connected means `lk({b}, Δ(ℰ(b))_[{b},v])` is `(−1)`-connected, i.e. nonempty, for every
  `v ⪈ {b}`. Its vertices are the `w ∈ ℰ(b)` with `{b} ⪇ w ≤ v`. Prop. 8.10 with `n ≥ 1` and Thm 8.2 both
  supply this, together with finiteness of every `ℰ(b)`.
- **Charts are S-maps with domain images.** Classes of expansions of `[id, R_τ]` are `[h, E]` with `h` a
  composite of S-maps (Def. 4.18), so each chart `c = hκ_E` is an S-map. Its image is a proper subdomain of `R_τ`,
  since `w ⪈ {b_τ}` has at least two disjoint classes.
- **Item 1 (chart lemma).** Each step is justified:
  - Prop. 4.22(1),(2) splits `q` along `w`.
  - Prop. 4.24(2) pulls back by `c_j^(-1)`, because `c_j^(-1)·[c_j, R] = [id, R]`.
  - Rank drops because `|w| ≥ 2`, and composability is checked.
- **Item 2 (prefix connectors).** Lemma 4.25 and Cor. 4.26 give the common bound. The normal form uses Def. 4.10
  with `κ_E ∈ 𝕊(R_(t(E)), E)`, and equal classes over representatives force equal types and an `h ∈ H_ρ`.
- **Item 3 (finite tables).**
  - `h·b_τ = [h, R_τ] = b_τ` for `h ∈ H_τ`, so Def. 6.1(3) makes `H_τ` permute the finite set `ℰ(b_τ)`, and
    `hc = c′k` holds with `c′` a chart of `h·w`.
  - Transition rules come from common bounds of pairs of systems.
- **Why this closes the twisted door.** The review 79ad158419 found twisted connectors unbounded in tree
  coordinates, where sections are taken along tree prefixes with arbitrary `κ_ω`.
  - Chart coordinates never use deep `κ_ω`. Deep domains are reached by chart words over a **finite** chart set,
    and a twist becomes a change of chart system, recorded in the finite table.
  - FH's Röver certificate, Ex. 4.35, is exactly this case: `b c_0 = c_0 a`, with `c_0 a` a chart of the
    nonstandard system.

## 4(a). The orbit cap: the missing length bound, repaired for nested certificates

**The gap.** The sketch asserts that address lengths stay `≤ ℓ_0 + O(n)`, and nothing written proves it.
- Addresses are mixed-system chart words, which are not unique.
- Test (B) rewrites prefixes by transition rules `cω = c″ω″h` with `|ω| ≠ |ω″|` in general.
- Deciding which refinement piece applies can cascade to the end of the address, since every level may need a
  transition.
- A per-step length change linear in the address length would give doubly exponential time.

**Repair (nested case).** Assume the compact ultrametric property, Def. 3.12. The seed application has it
anyway, since `finitary-permutations-force-singleton-domains` assumes it.
- **The domain tree.** The domains inside `R_τ` form a rooted tree, with children the maximal partitions
  (Cor. 3.20, Prop. 3.16). S-maps preserve maximal partitions (Prop. 3.24), so they preserve relative depth:
  `depth(c(E)) = depth(c(R_ρ)) + depth_(R_ρ)(E)`.
- **Length is at most depth.** Every chart maps onto a proper subdomain, so it adds at least 1 to the depth. So
  **every chart address of a point `y` has length at most the tree depth of `{y}`**, whatever systems it uses and
  however the cascade rewrote it.
- **Depth grows linearly.** `H_τ` preserves depth, and each generator changes depth by a bounded amount: in item 2
  the prefix chart swap has bounded length. So after `n` generators the depth, and therefore every address used
  in the cascade, is `≤ d_y + O(n)`.
- **Total cost.** The recursion then costs `T(ℓ) ≤ U·B·T(ℓ−1) + 2^(O(ℓ))`, where `U` bounds the lengths in the
  transition rules and `B` the number of refinement pieces. Carried `H`-words have length `≤ L^ℓ`, and they die
  at singleton types. So the total is `2^(O(n))`. **Item 4(a) holds for nested certificates.**
- **Not nested (e.g. product schemes, FH Prop. 6.23 and Ex. 8.4).** The depth argument is unavailable, and so is
  the singleton-domain input. Item 4(a) is **not established** there.

## 5. Structure groups

- **Nesting is needed.** Item 5 uses Cor. 3.20, Prop. 3.16 and Prop. 3.24, so it needs Def. 3.12, which the node's
  definition of "FH certificate" does not include.
- **The composition-factor claim is false as stated.** "Its finite quotients have composition factors of bounded
  order" fails: subgroups of `Aut(T_d)` include free groups, which have every finite group as a quotient.
- **Correct statement.** `H_τ` is residually finite, with a **separating family** of finite quotients (the level
  actions) that are subgroups of iterated wreath products of `S_d`. Only that family has composition factors of
  order at most `d!`. The "What survives" list should say this.
- **Two small overstatements in "What survives".**
  - The shallowest-moved-vertex depth `D(n)` gives an **upper bound** `2^(O(D(n)))` on `WP(H)`. So fast growth
    of `D` is necessary for hardness, not equivalent to it.
  - "Contracting ⇒ logarithmic depth" is correct.

## Scope for gate 1

- **Established.** The hard-seed form of gate 1 via Farley–Hughes is dead for every **nested** certificate that
  Thm 8.2 or Prop. 8.10 with `n ≥ 1` can use, with any structure groups, twisted or not. This subsumes the
  finite-type, self-similar and tree-coordinate caps.
- **Open.**
  - (i) Non-nested FH certificates, such as product or Brin-type schemes. There, neither the seed-address input nor
    the length bound is available.
  - (ii) Engines outside FH's theorems.
  - (iii) The word-problem channel through the `H_τ`, which the node correctly identifies as the survivor.

## Lesson for general BH

- **Finite expansion schemes are finite atlases.** This observation is right, and it removes the
  coordinate-coherence problem entirely.
- **What an atlas does not give.** An atlas bounds the alphabet, not the address length. In nested certificates the
  length bound comes from depth in the domain tree, which S-maps preserve. So "finite atlas plus depth-preserving
  charts" is the precise engine behind every exponential cap on main.
