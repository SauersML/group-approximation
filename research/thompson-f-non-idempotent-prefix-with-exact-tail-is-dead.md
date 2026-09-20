---
rg: 2
id: thompson-f-non-idempotent-prefix-with-exact-tail-is-dead
kind: claim
title: For the positive monoid of Thompson's F, an observation that reads the first I+D+1 trees through a tree invariant whose reachable states carry no idempotent probability — prefix depths or prefix sizes in particular — and every later tree exactly still has shadow defect zero
distinct_from:
  thompson-f-exact-tail-observations-have-zero-defect: that is the same statement for invariants whose reachable states DO carry an idempotent probability, where the tower coupling of its proof route is available; this is exactly the complementary case, which that route's Theorem C does not reach, and the two together are what "a certificate must read the exact prefix shapes" needs.
  thompson-f-prefix-observation-shadow-defect: that asks for the defect of the bounded prefix read exactly and nothing else (no tail at all), and a positive answer to it proves `thompson-f-is-not-amenable`; this reads the exact tail as well, is a refinement of that observation, and a positive answer here would say nothing about the root.
  thompson-f-flow-certificate-observation-gate: that is the minimax equivalence and its list of dead observations; this is one specific observation its Scope leaves open, singled out by the 2026-09-17 referee of `thompson-f-exact-tail-observations-have-zero-defect` as the gap between that node's theorem and that node's title.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills rules computed by a finite tree automaton run on the whole forest, and its Lemma 4.1 supplies the idempotent measure that is precisely what is unavailable here; the observation here is not finite-state, and the invariant reading its prefix is explicitly one with no idempotent state measure.
  thompson-f-degree-aware-automaton-flows-cannot-certify: that adds the total caret count and the negative part of a normal form to a finite-state profile, by a vine pump with a fair coin; here the prefix invariant may be unbounded (depth, size) and the tail is read exactly, so neither statement implies the other.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes non-amenability equivalent to doubling of `S_(m+1,m+d+1)`; this is a statement about which functions of a forest a transport rule may read, and proves neither answer.
---

**OPEN.** Notation as in `thompson-f-flow-certificate-observation-gate` and
`thompson-f-exact-tail-observations-have-zero-defect`: `S ⊆ M` finite, `I` the largest generator index
in the normal forms of `S`, `D = max_(s ∈ S) deg s`, `K = I + D + 1`. For a tree invariant
`(Q, δ, ℓ)` write `q(•) = ℓ`, `q(L ∧ R) = δ(q(L), q(R))`, and

`Ξ_(K,Q)(y) = ( (q(t_0), ..., q(t_(K−1))) , (t_K, t_(K+1), ...) )`.

**Statement.** `δ_1(Ξ_(K,Q)) = 0` for every tree invariant `(Q, δ, ℓ)` whose reachable states carry **no**
idempotent probability — a probability `π` on the reachable states with `δ_*(π ⊗ π) = π`.

**Why this is the live gap.** `thompson-f-exact-tail-observations-have-zero-defect-proof` proves
`δ_1(Ξ_(K,Q)) = 0` whenever an idempotent `π` *is* available: its model is a forest of i.i.d. depth-`H`
towers built over `π`, and Lemma 4.2 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` is what makes each split-off subtree
carry the same state law as a fresh tree. Only with that in hand does the coupling of `split_s Y` at
`N = n` with `Y` at `N = n + d` become an exact identity on the prefix state vector. Without it the
model has nothing to say. So the conjunction of that node's Theorem C with this claim is exactly what
its title asserts — "a flow certificate must read the exact shapes of the first `K` trees" — and that
conjunction is what the 2026-09-17 referee found unproved (event `31e58aeb`).

**The invariants this is about are not exotic.** Three natural ones have no idempotent probability:
- *depth*, `δ(a, b) = 1 + max(a, b)`, `ℓ = 0`: an idempotent law would have
  `F(k) = P(depth <= k) = F(k − 1)^2` for all `k >= 1`, and `F` nondecreasing in `[0, 1]` forces
  `F ≡ 0` or `F ≡ 1` — neither is a probability with `F(−1) = 0`;
- *size* (number of carets), `δ(a, b) = 1 + a + b`, `ℓ = 0`: the least value in the support would have
  to satisfy `m = 1 + 2m`;
- *exact shape* itself, `δ = ∧`, `ℓ = •`: same argument, the least size in the support fails.

Each therefore escapes Theorem C while being a coarsening of no `Ξ_(K,Q)` covered by it, and
`Ψ(y) = ((depth t_0, ..., depth t_(K−1)), (t_K, t_(K+1), ...))` is the referee's explicit witness that
the conclusion "the residue is exactly `π_K`" does not follow.

**What a proof or a refutation would settle.**
- *Yes* (for every such `Q`), together with Theorem C, restores the full conclusion of
  `thompson-f-exact-tail-observations-have-zero-defect` as titled, and leaves
  `thompson-f-prefix-observation-shadow-defect` as the whole residue of the flow route.
- *No*, i.e. `δ_λ(Ξ_(K,Q)) > 0` for some such `Q` and some `λ > 1`, proves
  `thompson-f-is-not-amenable` outright, by Theorem A of the gate and Lemma 2.1(a) of
  `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` — a rule reading `Ξ_(K,Q)` is a rule
  reading a function of `y`, and the gate is exact for any observation. So a *no* here is at least as
  hard as the root, exactly as for `π_K`.
- Note that `δ_1(Ξ_(K,Q)) <= δ_1(π_K)` is **not** available: `Ξ_(K,Q)` is neither a coarsening nor a
  refinement of `π_K` (it blurs the prefix and sharpens the tail), so Lemma A.4 of the gate does not
  compare them.

## Attempts

- **The tower model of `thompson-f-exact-tail-observations-have-zero-defect-proof` (2026-09-17).**
  *Dies at Lemma 4.2:* the model needs the law of `q(u_c)` for a split-off depth-`(H − j)` tower to equal
  the law of `q(t)` for a fresh depth-`H` tower, which is what an idempotent `π` provides and what no
  invariant in this class admits. Concretely for depth: `split_s` replaces a tree of the prefix by
  subtrees of depth `H − j`, `1 <= j <= d`, while the positions shifting in from the right carry fresh
  depth-`H` towers, so the two prefix depth vectors differ deterministically.
- **Randomising the tower depth.** *Dies at the correlations:* several prefix positions of `split_s Y`
  are subtrees of one tree `t_a`, so their depths are perfectly correlated on the split side and
  independent on the other. Recorded in the same words in the `## Attempts` section of
  `thompson-f-prefix-observation-shadow-defect`, which is the same obstruction seen through the prefix
  rather than through the invariant.
- **Coarsening from a dead observation.** *Dies immediately:* by Lemma A.4 of the gate the dead
  observations form a down-set, and `Ξ_(K,Q)` for a non-idempotent `Q` is a coarsening of no observation
  yet known dead — that is precisely the content of the referee's counterexample class.
- **Tower law with depth-`(d + r)` tops (2026-09-20, swarm-0917-w21-w21-f-break).**
  - *Settles every bounded-depth invariant.* See
    `thompson-f-bounded-depth-subtree-profiles-have-zero-defect`. For every Guba set and every `r`, the
    observation that reads each prefix tree to depth `r`, the size and depth of every subtree rooted at
    depth `<= r`, and the exact tail, has `δ_1 = 0`. So every `Q` computed from a bounded-depth profile
    is dead: sizes, depths, root splits, and size tables to any fixed depth.
  - *Dies at unbounded depth, and must.* Exact shape (`δ = ∧`) is in this node's own class, as the
    third bullet above notes. So the statement "for every such `Q`" contains `δ_1(π_K) = 0`. By
    `thompson-f-prefix-observation-is-lossless`, that is amenability of `F`. As titled, the node is
    therefore equivalent to `thompson-f-is-amenable`.
  - *The live residue* is the invariants strictly coarser than shape that no bounded-depth profile
    computes. Arm lengths are the first example: they are cheap by an i.i.d. arm law, sketched but not
    claimed in the Scope of the new node.
