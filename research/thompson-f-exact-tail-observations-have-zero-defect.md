---
rg: 2
id: thompson-f-exact-tail-observations-have-zero-defect
kind: claim
title: An observation of the positive monoid of Thompson's F that reads every tree of the forest exactly except that it blurs the first I+D+1 trees through a finite automaton has shadow defect zero, so a flow certificate must read the exact shapes of a bounded prefix
distinct_from:
  thompson-f-flow-certificate-observation-gate: that establishes the minimax equivalence between a flow rule reading `Ψ` and positive shadow defect, and lists as dead the coarse observations (constants, Schreier cosets, automaton profile plus tree count plus total caret count); this adds a new dead observation whose data are unbounded and exact on all but finitely many trees, which that claim's Scope explicitly leaves open ("observations reading unbounded data of individual trees (sizes, depths, shapes)"). It uses that claim's Corollary A.2 as its only gate input.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills rules computed by a finite tree automaton run on the whole forest; the observation here is not finite-state — it returns the exact shapes, hence the exact sizes, depths and subtree structure, of every tree from position `I + D_S + 1` on.
  thompson-f-degree-aware-automaton-flows-cannot-certify: that adds the total caret count and the negative part of a normal form to the finite-state profile, by a vine pump with a fair coin; the observation here is incomparable — it forbids the total caret count (Section 5) and instead reads the tail exactly.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes non-amenability equivalent to doubling of `S_(m+1,m+d+1)`; this is a statement about which functions of a forest a transport rule may read, and proves neither answer.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is a Schreier-graph amenability statement on coset spaces of `F`; this is a shadow law on the positive monoid, and the observation is not a coset map.
---

**OPEN** — refereed 2026-09-17 and refuted **on scope, not on arithmetic**; see `## Attempts`. The
attempted proof is kept in `thompson-f-exact-tail-observations-have-zero-defect-proof`. Its Theorems C
and D survive (after one hypothesis repair in Lemma 1), but they establish strictly less than the title
and the boxed claim below assert: they kill the exact tail only when the prefix is read through a tree
invariant whose reachable states carry an **idempotent** probability, and prefix depths and prefix sizes
admit no such measure. So the conclusion "a flow certificate must read the exact shapes of a bounded
prefix" is *not* proved, and the residue is larger than `π_K`. Read the statements below with that
correction; the title is left unchanged so that the refuted assertion stays on the record.

**Setting (verbatim from the gate).** `M` is the positive monoid of `F`, identified with forests
`y = (t_0, t_1, ...)`. For finite `S ⊆ M` and `Ψ : M → X`, a *rule reading `Ψ`* is `w(s, y) = G(s, Ψ(y))`
with `G >= 0`; for probability vectors `μ, η` on `M`, `ρ^η_s(y) = η(s y)`,

`D_λ(μ, η) = Σ_(s ∈ S) || (Ψ_* μ − λ Ψ_* ρ^η_s)_+ ||`,   `δ_λ(Ψ) = inf_(μ, η) D_λ(μ, η)`.

**Notation.** For finite `S ⊆ M`, `I = I(S)` is the largest generator index in the normal forms of `S`,
`D = D_S = max_(s ∈ S) deg s`, and

`K = K(S) = I + D + 1`.

For `S = S_(m+1,m+d+1)` (the monomial sets of `thompson-f-nonamenable-iff-some-monomial-set-doubles`),
`I = m + d − 1`, `D = d`, so `K = m + 2d`.

**Theorem C (exact tail).** Let `(Q, δ, ℓ)` be any tree invariant whose reachable states carry an
idempotent probability `π` — in particular any finite one, by Lemma 4.1 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`. Define

`Ξ_(K,Q)(y) = ( (q(t_0), ..., q(t_(K−1))) , (t_K, t_(K+1), t_(K+2), ...) )`.

Then `δ_1(Ξ_(K,Q)) = 0`. Consequently, by Corollary A.1 of the gate, no rule reading
`Ψ = Θ ∘ Ξ_(K,Q)`, for any function `Θ`, is a certificate with ratio `> 1`, and no such rule proves
`thompson-f-is-not-amenable`.

**Theorem D (both endpoint germs).** The same holds for

`Ξ⁺_(K,Q)(y) = ( Ξ_(K,Q)(y) , depth of the leftmost leaf of t_0 )`,

that is, `Ξ_(K,Q)` together with the germ datum of `y` at the endpoint `0` (the leftmost-leaf depth
of `t_0`, which determines the slope at `0` up to the orientation convention). The germ datum at `1` is
the rightmost-leaf depth of the last nontrivial tree, which `Ξ_(K,Q)` already reads exactly whenever
`N_y > K`.

**What this says.** The observation is *not* coarse: it returns the exact shape — hence the exact size,
depth, subtree structure and every unbounded invariant — of every tree of the forest except the first
`K`, plus a finite-state reading of those `K` and the germ at `0`. It is therefore only finitely far
from `id_M`, whose defect is positive exactly when `F` is not amenable (gate, Corollary A.3). So:

> every flow certificate for `S` must read the **exact shapes of the first `I + D_S + 1` trees**.
> Reading the whole rest of the forest exactly, however finely, contributes nothing.

Equivalently, writing `π_K(y) = (t_0, ..., t_(K−1))` for the *prefix observation*, the fibers of `π_K`
carry no certificate power. The splits `split_s` for `s ∈ S` descend to well-defined partial maps
`σ_s` on `K`-prefixes (Lemma 1 of the proof), so the flow problem is a skew product of a finite-window
system `(X_K, {σ_s})` over a shift of the tail, and Theorem C says the base shift is inert.

**Sharpness.** `K` cannot be lowered to `K − 1`: for `S = S_(2,3) = {x_0, x_1}` and `s = x_1`, the model
of the proof gives total variation `15/16` for the observation that blurs only the first `K − 1` trees
(exact arithmetic, `experiments/thompson-f-shadow-defect-2026-09-17/output.txt`). The reason is
structural: for `s` of degree `d` whose splits fall on index `I`, the tree at position `I + d` of
`split_s Y` is a proper subtree of `t_I`, and its depth differs from that of a fresh tree.

**What is not covered, exactly.**
1. *The total caret count together with the exact tail.* The two cannot be absorbed by one model of this
   family: the padding that Theorem B of the gate uses to free the caret count is a right comb placed in
   the tail, and the exact tail pins it down. Section 5 of the proof shows the obstruction is not an
   artifact of the choice of padding — the first-block caret sums differ by `d` i.i.d. summands, not by
   a bounded shift. Whether `(Ξ_(K,Q), |y|)` is dead is open.
2. *The prefix observation `π_K` itself.* `δ_λ(π_K) > 0` for some `λ > 1` would prove
   `thompson-f-is-not-amenable` (Theorem A of the gate with Lemma 2.1(a) of
   `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`), so it is at least as hard as the
   root; and `δ_1(π_K) = 0` is not proved here. This is recorded as
   `thompson-f-prefix-observation-shadow-defect`. It is *one* piece of the residue, not the whole of it:
   see `## Attempts` — every (prefix invariant with no idempotent state measure, exact tail) pair, such
   as prefix depths or prefix sizes, is equally untouched.
3. *Group-side flows* (reduced pairs of forests), unchanged from the gate's Scope.

**Calibration.** In the free monoid `{a, b}*` the constant rule `w ≡ 1` is a certificate with ratio 2,
and the proof breaks at its first step: `Y ∈ ∩_(s ∈ S) sM` uses the Ore property of `M`, which
`{a, b}*` lacks. The theorem proves neither answer for `F`: it removes a class of witnesses for
`thompson-f-is-not-amenable`, and the same construction runs verbatim in any monoid with the Ore
property and the forest presentation, including ones whose groups are known non-amenable only through
data outside the observation.

**Computation.** `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py` (stdlib,
exact `Fraction` arithmetic, output in `output.txt`):
1. the monoid relations and the 462 normal forms of degree `<= 5` in `x_0..x_5`;
2. the split geometry of the proof for `S_(2,3)`, `S_(2,4)`, `S_(3,4)`, `S_(3,5)`, `S_(4,6)`, `S_(2,5)`,
   `S_(3,6)`: every `split_s Y` is defined, the tree count rises by `deg s`, positions `>= I + d + 1`
   are untouched, the first `I + d + 1` addresses form an antichain of depth `<= d < H` inside
   `t_0 .. t_I` that exhausts their bottom leaves, and the leftmost-leaf depth drops by exactly
   `j_0(s) = #{j : i_j = 0}`;
3. the exact conditional total variations for `S_(2,3)`, over all `16^4` and `16^5` model atoms.
   `Ξ_K` and the profile with the tree count give `0`. The observations that survive this model give
   `Ξ_(K−1)` `15/16`; prefix `π_K` `255/256`; `id_M` `255/256`; `(Ξ_K, |y|)` `3885/4096`; sorted tree
   sizes `253125/262144`; profile with tree count and caret count `219765/262144` (that last one is
   dead by Theorem B of the gate, whose comb padding this model omits);
4. the germ-at-`0` mixtures of Theorem D, with total variation `j / (L'' + 1)` for `j = 1, 2, 3`.

## Attempts

- **The exact-tail tower coupling (2026-09-17), refereed and refuted on scope.** The route
  `thompson-f-exact-tail-observations-have-zero-defect-proof` is kept as the attempt. Three referees;
  two recorded *survives* under the hypotheses/citations lens and the calibration lens, one recorded
  *refuted* (event `31e58aeb`) and that reason stands. All three reran
  `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py` and reproduced
  `output.txt` byte-identically (`Ξ_K` `0` for both `s`, `Ξ_(K−1)` `15/16`, `π_K` = `id_M` `255/256`,
  `(Ξ_K, |y|)` `3885/4096`, germ mixtures `j/(L'' + 1)`), and `bin/cairn check` compiles the node — the
  arithmetic is not in dispute.
  - *What stands.* `δ_1(Ξ_(K,Q)) = 0` and `δ_1(Ξ⁺_(K,Q)) = 0` for every tree invariant `(Q, δ, ℓ)` whose
    reachable states carry an idempotent probability `π`, with `K = I + D + 1`, once Lemma 1's
    hypothesis is repaired (below). Lemma 2 really is an exact identity, not an approximation: since
    `K >= I + d + 1`, position `a >= K` of `split_s Y` carries `t_(a − d)`, so the split-side prefix
    reads only `t_0 .. t_(K − 1 − d)` and the tail only `t_(K − d) .. t_(n − 1)` — disjoint families, so
    both sides factor as `K` i.i.d. `π` states tensor `(n + d − K)` i.i.d. depth-`H` towers, the `V_n`
    have disjoint supports because the exact tail reveals `N`, and the whole `ℓ^1` cost is `2d/R_L`.
    The `K − 1` sharpness stands as a statement about this model family only (the proof body hedges
    this; the Sharpness headline above does not). `thompson-f-not-amenable-from-prefix-defect` uses only
    Lemma A.4 and is unaffected.
  - *Repair needed in Lemma 1 (split geometry).* The clause "at a node of depth `<= j < H`, which is
    therefore internal to one of `t_0, ..., t_I`" does not follow from the stated hypothesis
    "`t_0, ..., t_I` all have depth `>= H`": depth `>= H` does not make every node of depth `< H`
    internal, so `split_s` can be undefined. Witness in the repo's own code: `S = {x_0 x_0}`
    (`I = 0`, `D = d = 2`, `H = 3`, `K = 3`), `t_0 =` leaf `^` (complete depth-2 tree) has depth
    `3 >= H` and `N_y = 5 > K`, yet `split_word(y, (0, 0))` returns `None`. The hypothesis must read
    "complete to depth `H`" (every node of depth `< H` internal), which the Section 2 towers satisfy, so
    Theorems C and D survive the repair.
  - *The load-bearing non-sequitur (the reason for the refutation).* Theorem C proves
    `δ_1(Θ ∘ Ξ_(K,Q)) = 0` only for invariants whose reachable states carry an idempotent probability.
    The title, the boxed "What this says", and Section 6 of the proof ("the residue is therefore exactly
    the base") assert strictly more. Counterexample class inside the gate's own language:
    `Ψ(y) = ((depth t_0, ..., depth t_(K−1)), (t_K, t_(K+1), ...))`. It reads no exact prefix shape and
    is a coarsening of no `Ξ_(K,Q)`, because depth (`δ(a, b) = 1 + max(a, b)`, `ℓ = 0`) admits no
    idempotent probability — `F(k) = P(depth <= k)` would satisfy `F(k) = F(k−1)^2`, forcing `F ≡ 0` or
    `F ≡ 1` — and the same argument kills size (`δ(a, b) = 1 + a + b`) and exact shape. So a flow
    certificate need **not** read exact prefix shapes, and the residue is not `{π_K, (Ξ, |y|),
    group-side flows}`: it is the whole interval between idempotent-carrying prefix observations and
    `id_M`, i.e. every (non-idempotent prefix invariant, exact tail) pair. `(Ξ_K, |y|)` of Section 5 is
    one member of that family (with the tail exact, `|y|` is the prefix caret sum), and the Attempts
    section of `thompson-f-prefix-observation-shadow-defect` leans on the same fact ("several prefix
    positions are subtrees of one tree `t_a`, so their depths are perfectly correlated on the split
    side"). Hence the framing of that node as "the one observation left", and the Consequence bullet in
    `research/thompson-f-is-not-amenable.md`, are false as stated and have been corrected there.
  - *The defensible statement*, i.e. what a re-established version of this node should say: **an
    observation reading the prefix through any idempotent-carrying tree invariant and the tail exactly
    has shadow defect zero** — not "the tail is inert, so only the exact prefix remains".
  - *Smaller prose defects, recorded so they are not re-introduced.* (a) "the only import is
    Corollary A.2" is inaccurate: Corollary A.1, Lemma A.4 and Lemmas 4.1/4.2 of
    `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` are used too, though all lie
    inside the route's declared `requires`, so no undeclared dependency exists. (b) "Reading the whole
    rest of the forest exactly, however finely, contributes nothing" and "the fibers of `π_K` carry no
    certificate power" assert `δ(π_K) = δ(id_M)`, which is open question 2 of this same file — `δ` is
    not subadditive over a factorisation. (c) "gate, Lemma 2.1(a)" misplaces Lemma 2.1, which lives in
    `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` and needs Theorem A of the gate
    alongside it; `thompson-f-not-amenable-from-prefix-defect` cites both correctly.
