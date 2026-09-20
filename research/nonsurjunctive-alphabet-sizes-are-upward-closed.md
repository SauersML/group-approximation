---
rg: 2
id: nonsurjunctive-alphabet-sizes-are-upward-closed
kind: claim
title: A group that is not surjunctive over k symbols is not surjunctive over any larger alphabet
distinct_from:
  strict-rule-pairs-ascend-to-larger-alphabets: that is ascent with the tables fixed, for arbitrary table pairs, and it is refuted; this is ascent for one group, where the memories and the realized tables may change.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that proves NS(G) closed under multiples and equal to NS_all on existentially closed groups; this asks for closure under every larger size.
  surjunctivity-failure-descends-to-binary-alphabet: that moves the failing size down to two; this moves it up to every larger size.
  table-pair-strict-exactly-at-composite-alphabet-sizes: that is one table pair, realized in no group, whose admissible sizes are the composites; this is ascent for realized data, which that example cannot decide.
artifacts:
  - research/artifacts/composite-size-strict-table-2026-09-16.md
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: for every group `G`, if `k ∈ NS(G)` and
`n >= k`, then `n ∈ NS(G)`. The memories and the realized tables may change.

**Place in the graph.**
- It is the group-level consequence formerly recorded under `strict-rule-pairs-ascend-to-larger-alphabets`. That
  table-level claim is refuted by `table-pair-strict-exactly-at-composite-alphabet-sizes`.
- With `every-group-is-surjunctive-over-binary-power-alphabets` it gives the conjecture
  (`gottschalk-via-upward-closed-nonsurjunctive-sizes`).
- The invalidated route `linear-sofic-surjunctivity-via-formalizability-and-ascent` used only this group-level statement
  for the group at hand, so it can be rebuilt over this claim.
- It holds vacuously if the conjecture holds.

## Attempts

- **Fixed tables** (swarm, 2026-09-16). This was the refuted claim `strict-rule-pairs-ascend-to-larger-alphabets`. A
  2 x 3 table pair is strict exactly at the composite sizes (`table-pair-strict-exactly-at-composite-alphabet-sizes`).
  - What the example is not. It is not realized in any group, since `x_b = 1` forces `(1,a) ~ (b,a)` in the reverse
    table, and the two-digit code needs that coincidence to fail.
  - What it forces. A proof must use that the tables come from a group, or must change the tables, for instance by
    enlarging the memories.
  - Realized pairs cannot help. A table pair realized in a group with any strict size already refutes the
    conjecture, so realized-table ascent cannot be refuted by any example short of that.
  - Artifact `research/artifacts/composite-size-strict-table-2026-09-16.md`, Section 4.
- **Multiples only.** `ec-groups-share-the-nonsurjunctive-alphabet-sizes` gives `k l ∈ NS(G)` for every `l >= 1`, and no
  more. The smallest instance not covered is `k ∈ NS(G)` implies `k + 1 ∈ NS(G)`, for example `2` implies `3`.
- **Passive extensions are dead at group level.** `passive-fixing-injective-automata-are-surjective`: an injective
  automaton that fixes the added symbols in place and writes no added symbol at an original site is surjective. So the
  walls design recorded under `strict-rule-pairs-ascend-to-larger-alphabets` cannot be repaired. An ascent from `A` to
  `A ⊔ D` must write at `D`-sites, or write `D`-symbols at `A`-sites.
- **Existentially closed groups.** `NS(K) = NS_all` for existentially closed `K`, so the claim for one such `K` says
  exactly that `NS_all` is upward closed. That universal form already suffices for the route to the conjecture. The
  per-group form is needed for per-group applications such as linear soficity.
- **Moving one extra bit** (a-gs-upward-closed, 2026-09-17). The design: split one letter `a0` of a strict `τ` into
  `|Q|` letters, and carry the extra data along a local matching of `a0`-sites, or by any injective map that copies
  it by a translation away from the defects. It dies over every group, by
  `translating-transport-split-lifts-are-surjective`.
  - The step where it dies. The lift forces `τ(a0^G) = a0^G`. The cofinite translation makes the finite injection
    `Q^{F \ E} -> Q^{Fs \ E'}` count `|E(τ u)| <= |E(u)|`. Charge noncreation then makes `τ` and the lift surjective.
  - What survives among lifts.
    - One-letter splits whose rest bit map `T_0` on `Q^G` is a bijective automaton that is not a relabelled
      translation. If `T_0` is not surjective, then `|Q| ∈ NS(G)` already.
    - Splits of two or more letters. The charge is then degenerate, and the product lifts giving the multiples sit
      here.
    - Ascents that commute with no letter collapse.
  - By-product. `reversible-automata-that-never-lower-rest-counts-preserve-them` holds over every group, by
    `rest-count-preservation-from-charge-noncreation`. So the count-raising hypothesis of
    `count-raising-reversible-automata-lower-biased-rokhlin-entropy` is never met, and the autonomous star designs die
    unconditionally.
- **Any letter-collapse lift, any rest map** (swarm-0917-w4-gs-upward, 2026-09-17). The first survivor above is
  dead too, and so is the whole collapse class for `k -> k+1`, unless `2 ∈ NS(G)`. By
  `collapse-lifts-with-unique-largest-fiber-are-surjective`, if `Φ` is injective on `B^G`, `r ∘ Φ = τ ∘ r` for a
  letter collapse `r : B -> A` and an injective `τ`, and the largest fiber `Q0` is unique, then either
  `|Q0| ∈ NS(G)` or `τ` and `Φ` are both surjective.
  - The step where the class dies. The rest map `T_0 = Φ|_{Q0^G}` is an injective automaton. If it is not
    surjective, `|Q0|` already fails. If it is bijective, it preserves the uniform Bernoulli measure
    (`bijective-ca-preserve-uniform-bernoulli-measure`). A window count over a finite defect then gives
    `W(τ u) <= W(u)` for the charge `w(a) = log(|Q0| / |Q_a|)`, and charge noncreation makes `τ` and `Φ` surjective.
    The translation of the earlier attempt is no longer needed.
  - Invariant. The fiber charge `W(u) = Σ_g log(|Q0| / |Q_{u(g)}|)`: every collapse lift with a bijective rest map
    conserves it.
  - For `n = k + 1`. Every collapse `B -> A` has a unique fiber of size `2`. So over a group with `2 ∉ NS(G)`, an
    ascent `k -> k+1` must not commute with any letter collapse onto an injective automaton. If `2 ∈ NS(G)`, the
    step `k -> k+1` is needed only for even `k`, because odd `k` gives even `k+1` as a multiple of `2`.
  - What survives. (i) Collapses with at least two largest fibers, for example `(2,2,1)` from `3` to `5`, and the
    product lifts. (ii) Ascents with no collapse onto an injective automaton, for instance lifts over a
    non-injective `τ'`, or block-code factors instead of letter maps.
  - By-product (descent). A strict automaton on `n >= 3` symbols with one autonomously evolving letter, whose
    occurrence set moves by an injective binary automaton, gives `n - 1 ∈ NS(G)`.
- **Dual background, smallest fiber** (swarm-0917-w5-gs-upward, 2026-09-17). This kills survivor (i) above whenever the
  smallest fiber is unique, including the named example `(2,2,1)` from `3` to `5`. By
  `smallest-fiber-collapse-lifts-are-surjective` (established, route `smallest-fiber-collapse-dual-background-proof`),
  suppose `r ∘ Φ = τ ∘ r` with `τ` bijective, `Φ` injective, and a unique smallest fiber `Q0` of size `s`. Then
  `s ∈ NS(G)` (only possible if `s >= 2`), or `Φ` is surjective.
  - The step where the class dies. Replace `Φ` by a power fixing every constant. The rest map on `Q0^G` is then
    bijective, or `s` already fails. The same window count as before gives `W'(u) <= W'(τ u)` with
    `w'(a) = log(|Q_a| / s)`. That is the opposite sign, so it controls `τ^{-1}`, not `τ`. `τ^{-1}` is an automaton that
    fixes `a0^G`, preserves finiteness and never creates `W'`. Charge noncreation gives equality, and the fiber
    injections become bijections.
  - Invariant. The fiber charge relative to the smallest fiber, `W'(u) = Σ_g log(|Q_{u(g)}| / s)`.
  - Consequence for ascent. Suppose a strict collapse design sits over a bijective base, and neither extreme fiber size
    already lies in `NS(G)`. Then it needs two letters of the largest size and two of the smallest (or equal
    fibers). The first undecided profile is `(2,2,1,1)`.
  - Autonomous region. Let `j < n/2` letters have an occurrence set that moves by an injective automaton. Then a strict
    automaton on `n` letters gives `n - j ∈ NS(G)`, and `2 ∈ NS(G)` or `j ∈ NS(G)`. So over a group with
    `2 ∉ NS(G)`, ascent `k -> k + j` by an autonomously moving region of `j < k` new letters needs `j ∈ NS(G)`.
    The case `j = 1` recovers the dead star designs.
  - What survives.
    - Profiles with two letters of each extreme size.
    - A base `τ` that is strict but on fewer letters (`|A| ∈ NS(G)`, which says nothing about `n`).
    - Block-code factors.
    - Coupled dynamics with no factor onto an injective automaton.
- **Tied largest fibers, arbitrary base** (swarm-0917-w17-w17-gs-break, 2026-09-19). This kills every profile in the
  letter-collapse class, including `(2,2,1,1)` and every tie, and it drops the bijective-base assumption. By
  `collapse-lifts-with-tied-largest-fibers-are-surjective` (established, route `tie-collapse-sea-jacobian-proof`),
  suppose `r ∘ Φ = τ ∘ r` with both injective, largest fiber size `q`, and `Z` the set of letters with fibers of
  size `q`. Then one of `q`, `|Z|`, `q|Z|` lies in `NS(G)`, or `Φ` is surjective.
  - Invariant. The charge `W(x) = Σ_g log(q / |Q_{x(g)}|)` on configurations with finitely many particles over an
    arbitrary `Z`-sea. `W` never increases. This comes from a Jacobian of `τ` on cylinders against the image of the
    uniform measure upstairs.
  - The step where the earlier argument stopped. With several largest letters, the background is the full shift
    `Z^G`, not a constant. Charge levels with two or more particles have infinite measure modulo translation, so
    measure preservation alone proves nothing there. Only single-particle levels, `W < 2 w_min`, close by
    compactness.
  - How it closes. Induct over the charge levels.
    - Split configurations are hit, by superposing preimages of the pieces with the inverse of `τ` on the sea.
    - The mass of the missing set equals the net flux out of the finite-measure set of `S_1`-connected
      configurations.
    - That flux equals an alternating sum of fluxes of product models over lower levels with independent seas,
      and each model flux is zero because `τ` is already bijective there. The weights are the linear
      coefficients of chromatic polynomials: `1` on far atom families, `0` on disconnected overlapping ones.
  - Consequence for ascent. A strict injective lift through a letter collapse never uses the failure of its base.
    It exists only when one of `q`, `|Z|`, `q|Z|` already fails, and all three are below `|B|` for a non-uniform
    profile. Single-letter doubling (`k -> k+1`, profile `(2,1,…,1)`) can therefore work only over groups with
    `2 ∈ NS(G)`. Ascent above the least failing size `n_0` by a collapse whose three sizes avoid `NS(G)` is
    impossible.
  - What survives.
    - Uniform profiles, where `q|Z| = |B|` and the statement is tautological.
    - Block-code factors that are not letter maps.
    - Coupled dynamics with no factor onto an injective automaton.
    - Lifts over a non-injective base `τ`, where Step 2 of the route fails because `r_* μ_B` is no longer
      compared with a measure-preserving base.
    - Designs whose three sizes already fail, which the theorem cannot touch.
- **Non-injective base, by fiber square** (swarm-0917-w18-w18-gs-break, 2026-09-19). This kills the survivor
  "lifts over a non-injective base". By `noninjective-letter-factors-force-squared-fiber-sizes` (established,
  route `noninjective-letter-factor-fiber-square-proof`), suppose `Φ` is injective with `r ∘ Φ = τ ∘ r` and `τ`
  is not injective. Then one of `q`, `qm`, `q^2 m` lies in `NS(G)`, where `m` is the number of largest fibers.
  - How it works. `Ψ = Φ × Φ` on the fiber square `(B ×_A B)^G` is injective. It is never onto, because two
    lifts of a `τ`-collision have an image pair whose only preimage leaves the fiber square.
  - The reduction. `Ψ` is itself a lift of the injective `Φ` through the first projection. That collapse has
    fibers `Q_{r b}`, so its largest-fiber count is `qm`, and the w17 theorem applies to the pair `(Ψ, Φ)`.
  - Invariant. The w17 sea charge of the first projection, `W(u) = Σ_g log(q / q_{r u(g)})` on `B`-configurations.
  - Combined with w17. Every injective automaton commuting with a letter collapse is bijective over a
    bijective base, or one of `q`, `m`, `qm`, `q^2 m` fails. Single-letter doubling `k -> k+1` needs
    `4 ∈ NS(G)`, whatever the base.
  - At the least failing size `n_0`, a strict automaton with a non-uniform letter factor has a non-injective
    factor, with `q^2 m ∈ NS(G)`.
  - By-products.
    - `Σ_a q_a^2 ∈ NS(G)`.
    - Fiber products of lifts multiply profiles pointwise: `Σ_a q_a c_a ∈ NS(G)`.
  - What survives.
    - Uniform profiles.
    - Block-code factors that are not letter maps.
    - Coupled dynamics with no letter factor at all.
    - Designs over groups where one of the four sizes already fails. For doubling, this means `4 ∈ NS(G)`.
      That is exactly the binary-power size excluded by the other premise of
      `gottschalk-via-upward-closed-nonsurjunctive-sizes`.
- **The first step `n0 -> n0 + 1`, by sink classes** (swarm-0917-w19-gs-follow, 2026-09-19, family
  minimal-counterexample). New ESTABLISHED `strict-automata-below-twice-the-minimum-have-one-sink-class`, with a
  self-contained reproof of upset descent. It does not prove the step. It classifies what a witness can look like, over
  any group `G` with `n0 = min NS(G)`.
  - Every proper upset of every `R(Ψ^p)` has at least `n0` letters. So below `2 n0` a strict automaton has one
    primitive sink class, and no exact sub-alphabet.
  - At `n0 + 1`, a strict `Ψ` is either robustly primitive (every `R(Ψ^p)` strongly connected) or has a power with a
    never-created letter. That letter is a singleton class, which gives `g = 1` and every `n >= n0^2 + 1` in `NS(G)`.
  - The invariant is the upset lattice of the powers.
  - Where ascent designs die.
    - A never-destroyed letter, including an exact one, dies at upset descent.
    - A design that keeps the old `n0` letters sitewise old is strict only if it already proves
      `some-nonsurjunctive-group-gives-a-binary-power-one`.
    - Under `every-group-is-surjunctive-over-binary-power-alphabets`, only robustly primitive witnesses remain, and
      the same holds at a second failing size `m2 < 2 n0` with `gcd(n0, m2)` a power of two.
  - What survives. Robustly primitive strict automata at `n0 + 1`, which carry the whole first step. Above `2 n0`
    several sinks are allowed.
- **Never-created ascents need only injectivity** (swarm-0917-w20-w20-gs-follow, 2026-09-20). By
  `injective-automata-with-inter-class-transitions-are-strict` (established, route
  `inter-class-arc-strictness-bernoulli-proof`), let `τ` be strict on `A^G` and `Φ` an injective automaton on
  `(A ⊔ D)^G` extending `τ` that never writes a `D`-letter at an `A`-site. Then `Φ` is strict, so
  `|A| + |D| ∈ NS(G)`.
  - Invariant. The clopen set `{x : x(1) ∈ U}` for an upset `U` of the transition digraph. Every automaton
    maps it into itself, and a bijective one preserves the uniform product measure. So a bijective automaton
    has only exact upsets, meaning no arc of its digraph joins two classes.
  - What it removes. For this class of ascents, strictness no longer needs its own proof. Every design where
    `A` is an upset reduces to building an injective extension. By the passive-fixing theorem, that extension
    must move or destroy `D`-letters.
  - Stronger form. An injective automaton over `G` with a letter that is never created but sometimes destroyed
    makes `NS(G)` cofinite. More generally, so does one with a class of size `1` and any arc between two
    classes. That gives ascent above every failing size at once.
  - What survives. The theorem constructs no injective extension. Two kinds of ascent are still untouched:
    - ascents that write new letters at old sites;
    - ascents whose digraph is a disjoint union of strongly connected pieces.
- **Where a never-created letter can be destroyed** (swarm-0917-w21-w21-gs-follow, 2026-09-20). The aim was to
  decide the cofinite branch left by w20: does some injective automaton destroy a letter it never creates?
  The result is `non-exact-transitions-of-injective-automata-are-wandering`, established by route
  `wandering-destruction-cylinder-proof`. The branch itself stays undecided.
  - Invariant. The cylinder of a non-exact pattern `P` for an upset `U`. Its `g`-letter is outside `U`,
    and every later image has it inside `U`. So the cylinder is wandering.
  - Consequences.
    - It has measure `0` for every invariant measure, including Cesàro limits of the orbit of the uniform
      measure.
    - It meets no `H`-periodic configuration with `[G:H] < ∞`, and no point of `NW(Φ)`.
    - An injective automaton is onto iff it is nonwandering. So the conjecture reads: every injective
      automaton is nonwandering.
  - Kill. Pushing the w20 measure argument from bijective to injective automata cannot decide the branch.
    Neither can finite-quotient or periodic-point searches. Their data coincide with those of a bijective
    automaton. The step where this dies: one needs an invariant measure, or a periodic point, that meets
    `[P]_1`, and none exists.
  - Reformulation. A never-created letter `c` is quiescent (`Φ(c^G) = c^G`), and its destruction shows up on a
    finite configuration over a `c`-background, where the count of non-`c` sites rises strictly.
    - So a witness is exactly a *charge-creating* injective automaton. It is the open reverse of
      `finite-injective-charge-noncreation-forces-surjectivity`.
    - For an ascent over a strict core `τ`, each configuration whose holes all fill in one step is sent
      into the Garden of Eden `A^G \ τ(A^G)`.
  - What survives.
    - Garden-of-Eden-type counting of the finite configurations of such an automaton, which would give the
      dual charge theorem.
    - Hole-filling constructions that spend the core's Garden of Eden.
    - Any argument that tracks the non-invariant orbit `Φ^k_* λ`. The uniform measure `λ` itself does
      charge the destruction cylinder.
- **Dual charge theorem, finite methods** (swarm-0917-w23-w23-gs-last1, 2026-09-20). This calibrates need `ebb50f1d`:
  an injective automaton with a quiescent, never-created letter `c` never raises the number of non-`c` sites.
  Proving that would empty the cofinite branch.
  - Result. `pre-injective-automata-can-destroy-never-created-letters` (established, route
    `pre-injective-automata-can-destroy-never-created-letters-proof`) has two parts.
    - Two letters: the need holds over every group, from finite injectivity alone, by charge noncreation over the
      dual background.
    - Three or more letters, over any group containing `F_2`: the need fails for pre-injective automata. On
      `{c} ⊔ Z/m`, the four tree slots `a, b` and `a^-1, b^-1` carry an injective pair `(α, β)`. A `c`-site with a
      non-`c` neighbour turns into the slot sum. One letter grows into five, and a leaf of the tree hull of any
      finite difference is read, in a separating slot type, by a neighbour whose other inputs agree.
  - Invariant and dying step. The invariant is injectivity on asymptotic pairs over every background. It is blind
    at `|A| >= 3`. The step that dies is the collision step of the charge-level induction: in the dual, images go up
    into levels not yet filled.
  - Consequence. A proof of `ebb50f1d` at `|A| >= 3` must use injectivity on pairs that differ at infinitely many
    sites. With lemma `2a3fa45c`, those pairs must also be neither periodic nor measure-typical. The example itself
    is not injective, by soficity of `F_2` and `reversible-automata-that-never-lower-rest-counts-preserve-them`.
  - Check. `experiments/dual-charge-calibration-2026-09-17/`. A binary search there finds no growth rule injective
    on subsets of the 2-ball in `F_2`, in line with the two-letter part.
