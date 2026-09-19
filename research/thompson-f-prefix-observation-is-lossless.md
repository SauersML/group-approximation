---
rg: 2
id: thompson-f-prefix-observation-is-lossless
kind: claim
title: For uniform-degree monomial sets of Thompson's F, truncating the forest tail never raises the shadow defect of an observation, so the prefix observation has exactly the defect of the identity and every exact-tail reading collapses to a prefix-only one
distinct_from:
  thompson-f-prefix-observation-shadow-defect: that asks whether delta(pi_K) > 0 for some S (item 1) and whether delta_1(pi_K) = 0 for all S forces delta_1(id_M) = 0 (item 2); this proves delta_lambda(pi_K) = delta_lambda(id_M) for every uniform-degree S, so item 1 is equivalent to non-amenability, item 2 is true, and the two are not separate pieces.
  thompson-f-exact-tail-observations-have-zero-defect: that proves zero defect for (idempotent prefix invariant, exact tail) by a tower coupling and was refuted on scope, with its remark "the fibers of pi_K carry no certificate power" recorded as open; this proves that remark, and gets that node's Theorem C for finite automata in one line from B.3 of the gate.
  thompson-f-non-idempotent-prefix-with-exact-tail-is-dead: that asks whether (non-idempotent prefix invariant, exact tail) is dead and says delta_1(Xi_(K,Q)) <= delta_1(pi_K) is not available; this proves delta(Xi_(K,Q)) = delta(q_K), with q_K the same prefix reading with no tail, hence the inequality with pi_K, and reduces that node to prefix-only readings.
  thompson-f-tree-size-observations-have-zero-defect: that pads prefix sizes and depths with an exact tail for width at most 3, and its Lemma 1 records that the tail shifts rigidly; this turns that rigid shift into an inequality between defects of any two observations, which removes the tail from that node's problem.
  thompson-f-stubborn-sets-split-off-the-tail: that splits stubborn sets and pivot orders over the tail at the level of finite sets (as does Lemma A of thompson-f-monomial-doubling-ratio-finite-universe-proof); this is the measure-level statement for flow observations, where a set-level splitting gives no bound on delta.
  thompson-f-flow-certificate-observation-gate: that is the minimax equivalence, and its Lemma A.4 compares an observation only with its coarsenings; this compares an observation with its tail truncation, which is neither a coarsening nor a refinement.
  thompson-f-is-not-amenable: that is the root; this proves neither answer.
artifacts:
  - experiments/thompson-f-prefix-lossless-2026-09-17/tail_truncation.py
  - experiments/thompson-f-prefix-lossless-2026-09-17/output.txt
---

**ESTABLISHED** through `thompson-f-prefix-observation-is-lossless-proof` (direct proof from the
definitions of the gate; not independently reviewed; no priority claimed).

**Setting (from the gate).** `M` is the positive monoid of `F`, identified with forests
`y = (t_0, t_1, ...)`, and `x_k y` merges roots `k` and `k + 1`. For finite `S ⊆ M` and `Ψ : M → X`,
`ρ^η_s(y) = η(s y)`, `D^Ψ_λ(μ, η) = Σ_(s ∈ S) ||(Ψ_* μ − λ Ψ_* ρ^η_s)_+||` and
`δ_λ(Ψ) = inf_(μ, η) D^Ψ_λ(μ, η)`. `I` is the largest generator index in the normal forms of `S`, and
`K = I + D + 1`.

Call `S` *uniform* if all its elements have one degree `d`. Every Guba set `S_(m+1,m+d+1)` is uniform.
Let `J = J(S) <= I` be the largest root of `s y` that holds a caret of `s`, over `s ∈ S`. For a Guba set
`J = m`. Let `τ_j(y)` be `y` with every tree at a position `> j` made trivial.

**Theorem (tail truncation).** Let `S` be uniform of degree `d`, `λ >= 1`, and `Ψ : M → X` any map. Then

`δ_λ(Ψ) <= δ_λ(Ψ ∘ τ_(J+d))`.

**Corollaries.** Let `S` be uniform.
1. **The prefix observation is lossless.**
   `δ_λ(π_K) = δ_λ(π_(J+d+1)) = δ_λ(id_M)` for every `λ >= 1`, where
   `π_k(y) = (t_0, ..., t_(k−1))`. For `S_(m+1,m+d+1)` the window has `m + d + 1` trees, not
   `K = m + 2d`.
2. **Item 1 of `thompson-f-prefix-observation-shadow-defect` is equivalent to non-amenability of `F`.**
   Its item 2 is **true**. The route `thompson-f-not-amenable-from-prefix-defect` is therefore a
   reformulation of the root, not a reduction of it.
3. **Exact tails add nothing.** Suppose `Ψ ∘ τ_(J+d)` is a coarsening of `Ψ`, as it is for every
   (prefix reading, exact tail) pair. Then `δ_λ(Ψ) = δ_λ(Ψ ∘ τ_(J+d))`. In particular, for any tree
   invariant `(Q, δ, ℓ)`, finite or not, idempotent or not,
   `δ_λ(Ξ_(K,Q)) = δ_λ(q_K) <= δ_λ(π_K)`, with `q_K(y) = (q(t_0), ..., q(t_(K−1)))` and no tail.
4. **Theorem C of `thompson-f-exact-tail-observations-have-zero-defect`, for finite `Q`, in one line.**
   `q_K` is a coarsening of the automaton profile, so by B.3 and A.4 of the gate `δ_1(q_K) = 0`, hence
   `δ_1(Ξ_(K,Q)) = 0`. There is no tower coupling and no repair of Lemma 1.
5. **The residue of the flow route, exactly.** For uniform `S`, every observation's defect is bounded
   by the defect of an observation that factors through `π_(J+d+1)`. The whole flow problem for `S` is
   therefore the finite-window partial-action system `(X_(J+d+1), {σ_s})`.
   - The open members of the family are the prefix-only readings `q_K` for invariants without an
     idempotent probability, such as depths and sizes, and `π_K` itself.
   - `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead` and
     `thompson-f-tree-size-observations-have-zero-defect` are each equivalent to their tail-free
     versions.
   - Among these, only `π_K` is known to be as hard as the root.

**What changes.**
- The picture recorded in the graph had two independently failing pieces: "1 could be true while every
  known prefix flow fails", and "2 could fail even if 1 has a negative answer". That picture is false.
  There is one piece, and it is the root.
- The worry that `σ_s` is not injective on `X_K`, so that in-sum counting on `X_K` differs from counting
  on `M`, does not matter. `δ` is defined by laws on `M`, and the theorem pushes those laws into the
  window without changing any split.
- The referee's point (b) on `thompson-f-exact-tail-observations-have-zero-defect` said that
  `δ(π_K) = δ(id_M)` is open because `δ` is not subadditive over a factorisation. The equality holds,
  and no subadditivity is needed.

**Scope.**
- The inequality needs one degree `d`. For a non-uniform `S` the two sides get truncated at different
  depths, and nothing is claimed.
- A.3 of the gate needs only the uniform Guba sets, so this costs nothing for the root.
- Proves neither answer to `thompson-f-is-amenable`.

**Computation.** `experiments/thompson-f-prefix-lossless-2026-09-17/tail_truncation.py` (stdlib, exact
rationals; output in `output.txt`).
- Checks the relation `x_j x_i = x_i x_(j+1)`.
- Checks facts (A) and (B) of the proof on all 3382 forests with at most 5 carets on 7 roots, for
  `S_(2,3)`, `S_(2,4)`, `S_(3,5)`, `S_(2,5)` and three random uniform sets. It confirms `J = m` on the
  Guba sets.
- Checks the identity `D^Ψ(μ', η') = D^(Ψ ∘ τ_(J+d))(μ, η)` exactly on random laws for three
  observations, including (prefix depths, exact tail), at `λ = 1` and `λ = 3/2`.

Proof route: `thompson-f-prefix-observation-is-lossless-proof`.
