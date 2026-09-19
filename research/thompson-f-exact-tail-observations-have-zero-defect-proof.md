---
rg: 2
id: thompson-f-exact-tail-observations-have-zero-defect-proof
kind: route
title: The splits of a finite S touch only the first I+D+1 trees, so a forest of i.i.d. idempotent towers can be coupled with a fresh one of I+d+1 more trees so that the two agree on every later tree exactly and on the automaton states of the prefix
target: thompson-f-exact-tail-observations-have-zero-defect
requires:
  - thompson-f-flow-certificate-observation-gate
  - thompson-f-finite-state-flows-cannot-prove-nonamenability
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
  - thompson-f-non-idempotent-prefix-with-exact-tail-is-dead
artifacts:
  - experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py
  - experiments/thompson-f-shadow-defect-2026-09-17/output.txt
---

Notation is that of `thompson-f-flow-certificate-observation-gate-proof`, which is that of Section 1 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`. `M` is the positive monoid of `F`,
identified with forests `y = (t_0, t_1, ...)`, all but finitely many trees equal to `•`; `x_k` acts by
`merge_k`; `s y = z` iff `split_s z := split_(i_d)( ... split_(i_1)(z))` is defined and equals `y`, for
`s = x_(i_1) ... x_(i_d)` in normal form. `N_y = 1 + max{a : t_a ≠ •}` and `N_e = 0`. `|y|` is the total
number of carets. For a tree invariant `(Q, δ, ℓ)`, `q(•) = ℓ` and `q(L ∧ R) = δ(q(L), q(R))`.

Throughout, `S ⊆ M` is finite and nonempty,

`I = I(S)` = the largest generator index occurring in the normal forms of `S` (`I = 0` if none),
`D = D_S = max_(s ∈ S) deg s >= 1`,  `H = D + 1`,  `K = I + D + 1`.

The one input from the gate is used verbatim:

> **Corollary A.2** (`thompson-f-flow-certificate-observation-gate-proof`). If for every `ε > 0` there
> is `μ ∈ P(M)` with `μ(∩_s sM) = 1` and `||Ψ_* ρ^μ_s − Ψ_* μ|| <= ε` for all `s`, then `δ_1(Ψ) = 0`.

Together with Corollary A.1 of the same file (`δ_1(Ψ) = 0` kills every rule reading `Ψ` with ratio
`> 1`) and Lemma A.4 (coarsening does not increase `δ`), this is all the gate machinery needed.

## 1. The splits move only a bounded prefix

**Lemma 1 (split geometry).** Let `y` be a forest whose trees `t_0, ..., t_I` are all **complete to
depth `H`** — every node of depth `< H` is internal — and with `N_y > K`, and let
`s = x_(i_1) ... x_(i_d) ∈ S`. Then `split_s y` is defined,

`split_s y = (u_0, ..., u_(I+d), t_(I+1), t_(I+2), ..., t_(N_y−1), •, ...)`,   `N_(split_s y) = N_y + d`,

where `u_0, ..., u_(I+d)` are the subtrees of `t_0, ..., t_I` rooted at an antichain of nodes
`v_0, ..., v_(I+d)` of depth `<= d < H`, listed left to right, whose bottom-leaf sets at depth `H`
partition those of `t_0, ..., t_I`. The addresses `v_c`, and in particular the depths `depth(v_c)`,
depend only on `s`, not on `y`.

*Proof.* This is the induction of Theorem 4.3 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`, in the form stated in Theorem B of
`thompson-f-flow-certificate-observation-gate-proof`. By induction on `j <= d`: after `j` splits the
forest is `(w_0, ..., w_(N_y + j − 1), •, ...)`, the `w_a` being the subtrees of `y` at an antichain of
nodes of depth `<= j`, in left-to-right order, with `w_a` the root of `t_(a−j)` for `a > I + j`. Step
`j+1` splits index `i_(j+1) <= I < N_y`, at a node of depth `<= j < H` of one of `t_0, ..., t_I`, which
is therefore internal **because those trees are complete to depth `H`**; the split is defined and
replaces that node by its two children, of depth
`<= j + 1`, preserving the antichain and the order, and leaving every `w_a` with `a > I + j + 1`
untouched. After `d` steps all nodes have depth `<= d < H`, so all `N_y + d` subtrees are nontrivial.
Only indices `<= I` are ever split, so the nodes lie in `t_0, ..., t_I`; being an antichain covering
those `I + 1` roots, their depth-`H` bottom-leaf sets partition. Each split is applied at an index
determined by `s`, and at each step the index determines which node of the current antichain is
subdivided, so the whole address list depends only on `s`. ∎

The last sentence is what makes the observation of the theorem readable: `split_s` descends to a
well-defined partial map on `K`-prefixes. Explicitly, put `π_K(y) = (t_0, ..., t_(K−1))`. Splitting
shifts trees to the right, so for `a < K` the tree `(split_s y)_a` is a subtree of some `t_b` with
`b <= I < K`; hence `π_K(split_s y)` depends on `y` only through `π_K(y)`, and so does the definedness
of `split_s y`. Write `σ_s` for that partial map of `K`-prefixes.

The script `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py` runs Lemma 1
symbolically on addresses for `S_(2,3)`, `S_(2,4)`, `S_(3,4)`, `S_(3,5)`, `S_(4,6)`, `S_(2,5)`,
`S_(3,6)` and checks each of its assertions (Stage 2 of `output.txt`).

## 2. The tail model

Let `(Q, δ, ℓ)` be a tree invariant whose reachable states `R` carry an idempotent probability `π`
(`δ_*(π ⊗ π) = π`). For finite `Q` one exists by Lemma 4.1 of the finite-state proof. Fix trees `T_r`
with `q(T_r) = r`.

*Tower.* For `h >= 0`, a *depth-`h` tower* is the complete binary tree of depth `h` with `T_(r_b)` hung
at its `b`-th bottom leaf, the `r_b` i.i.d. `π`. By Lemma 4.2 of the finite-state proof its state is
`π`-distributed. Let `θ_h` be its law (a law on trees).

*Parameters.* `n_0 = K + 1`, `L > n_0`, `R_L = L − n_0 + 1`.

*Model `μ_L`.* Draw `N` uniformly in `{n_0, ..., L}`; independently draw `t_0, ..., t_(N−1)` i.i.d.
`θ_H`; set `t_a = •` for `a >= N`, and `Y = (t_a)`. Since `H >= 1` every `t_a` with `a < N` is
nontrivial, so `N_Y = N`. The support is countable (finite, in fact, for each `N`). Every tree
`t_0, ..., t_I` is a depth-`H` tower, hence complete to depth `H` (every node of depth `< H` is a node
of the complete part, so internal), and `N > K`, so Lemma 1 applies and `Y ∈ ∩_(s ∈ S) sM`.

**Lemma 2 (conditional identity).** Fix `s ∈ S` of degree `d`, and `n ∈ {n_0, ..., L}`. Under the
observation

`Ξ(y) = ( (q(t_0), ..., q(t_(K−1))) , (t_K, t_(K+1), ...) )`,

the law of `Ξ(split_s Y)` given `N = n` equals the law of `Ξ(Y)` given `N = n + d`.

*Proof.* By Lemma 1, given `N = n`,

`split_s Y = (u_0, ..., u_(I+d), t_(I+1), ..., t_(n−1), •, ...)`, with `n + d` nontrivial trees.

Read off the two coordinates of `Ξ`.

*Tail.* Since `K = I + D + 1 >= I + d + 1`, position `a >= K` of `split_s Y` carries `t_(a−d)`. So the
tail is `(t_(K−d), t_(K−d+1), ..., t_(n−1), •, ...)`: exactly `n + d − K` nontrivial trees, i.i.d.
`θ_H`, followed by `•`. Given `N = n + d`, the tail of `Y` from position `K` is
`(t_K, ..., t_(n+d−1), •, ...)`: again `n + d − K` i.i.d. `θ_H` trees followed by `•`. Same law.

*Prefix states.* The first `K` trees of `split_s Y` are `u_0, ..., u_(I+d)` followed by
`t_(I+1), ..., t_(K−1−d)` (an empty list when `d = D`, since then `K − 1 − d = I`). Each `u_c` is, by
Lemma 1, a complete top of depth `H − depth(v_c) >= H − d >= 1` over the `T_r` hung below `v_c`, whose
states are i.i.d. `π`; so `u_c` is a depth-`(H − depth(v_c))` tower and `q(u_c) ~ π` by Lemma 4.2. The
`v_c` have disjoint bottom-leaf sets, so `q(u_0), ..., q(u_(I+d))` are independent; they involve only
the leaves of `t_0, ..., t_I`, so they are independent of `t_(I+1), ..., t_(n−1)`, whose states are
i.i.d. `π` as well. Hence the first-`K` state vector of `split_s Y` is i.i.d. `π` of length `K`. Given
`N = n + d`, the first-`K` state vector of `Y` is `(q(t_0), ..., q(t_(K−1)))`, i.i.d. `π` of length `K`.
Same law.

*Independence.* On the split side, the prefix states are functions of the leaves of
`t_0, ..., t_(K−1−d)` and the tail is `(t_(K−d), ..., t_(n−1))`; the two families of trees are disjoint,
hence independent. On the other side the prefix states are functions of `t_0, ..., t_(K−1)` and the tail
is `(t_K, ..., t_(n+d−1))`, again disjoint and independent. Two pairs of independent coordinates with
equal marginals have equal joint law. ∎

**Theorem C.** `δ_1(Ξ) = 0`, hence by Corollary A.1 of the gate no rule reading `Θ ∘ Ξ`, for any `Θ`,
is a certificate with ratio `> 1`.

*Proof.* Let `V_n` be the law of `Ξ(Y)` given `N = n`. The tail of `Ξ` has exactly `n − K > 0`
nontrivial entries, so the `V_n`, `n > K`, have pairwise disjoint supports. By Lemma 2 the law of
`Ξ(split_s Y)` is `R_L^(−1) Σ_(n=n_0)^(L) V_(n+d) = R_L^(−1) Σ_(n=n_0+d)^(L+d) V_n`, while
`Ξ_* μ_L = R_L^(−1) Σ_(n=n_0)^(L) V_n`. Disjointness gives

`|| Ξ_* ρ^(μ_L)_s − Ξ_* μ_L || = 2 d / R_L <= 2 D / R_L`.

All splits of `Y` are defined, so Corollary A.2 applies with `ε = 2 D / R_L → 0` as `L → ∞`. Finally
`Θ ∘ Ξ` is a coarsening, so `δ_1(Θ ∘ Ξ) <= δ_1(Ξ) = 0` by Lemma A.4. ∎

Stage 4 of `output.txt` is this identity checked by exhaustive exact arithmetic for `S = S_(2,3)`,
`n = 4`: over all `16^4` source atoms and `16^5` target atoms the conditional total variation is `0`
for both `s ∈ S`, while `id_M`, the prefix `π_K`, the sorted tree sizes and `(Ξ, |y|)` stay bounded away
from `0`.

## 3. Sharpness: the window `K` cannot be shortened

Let `Ξ'` blur only the first `K − 1` trees: `Ξ'(y) = ((q(t_0), ..., q(t_(K−2))), (t_(K−1), t_K, ...))`.
For `S = S_(2,3) = {x_0, x_1}` (so `I = 1`, `D = d = 1`, `K = 3`, `H = 2`) and `s = x_1`, Stage 4 gives
conditional total variation `15/16` — the model of Section 2 does not kill `Ξ'`. The mechanism is
general: for `s` whose splits all fall on index `I`, position `I + d` of `split_s y` carries the right
child of a node of `t_I` at depth `d − 1`, a top of depth `H − d`, whereas position `I + d` of a fresh
`Y` carries a top of depth `H`. Reading that tree exactly separates the two supports. So `K = I + D + 1`
is the exact window for this family of models.

## 4. The germ at `0`

**Theorem D.** Let `Ξ⁺(y) = (Ξ(y), λ_0(y))` where `λ_0(y)` is the depth of the leftmost leaf of `t_0`,
i.e. `−log_2` of the slope of `y` at `0`. Then `δ_1(Ξ⁺) = 0`.

*Proof.* Modify the model: draw, independently of everything else, `H_0` uniform in
`{H, H+1, ..., H + L''}` and let `t_0` be a depth-`H_0` tower; `t_1, ..., t_(N−1)` stay i.i.d. `θ_H`.
Lemma 1 still applies (`t_0` is a depth-`H_0` tower with `H_0 >= H` and `t_1, ..., t_I` are depth-`H`
towers, so all are complete to depth `H`), and its conclusion is unchanged.

Let `j_0 = j_0(s)` be the depth of the leftmost antichain node `v_0`. Since `v_0` is the leftmost node
of an antichain covering the roots of `t_0, ..., t_I`, it lies on the left spine of `t_0`; hence `u_0`
contains the leftmost leaf of `t_0` and

`λ_0(split_s y) = depth of the leftmost leaf of u_0 = λ_0(y) − j_0`.

By Lemma 1, `j_0` depends only on `s`; concretely `j_0(s) = #{j : i_j = 0}`, verified in Stage 2 of
`output.txt`. Also `0 <= j_0 <= d <= D`, and `u_0` is a depth-`(H_0 − j_0)` tower, so

`(q(u_0), λ_0(split_s Y)) ~ ψ_(H_0 − j_0)`,   `(q(t_0), λ_0(Y)) ~ ψ_(H_0)`,

where `ψ_h` is the joint law of (state, leftmost-leaf depth) of a depth-`h` tower. (Stage 5 of
`output.txt` checks both statements, by brute force against the recursion
`ψ_h(a, l) = Σ_(δ(a', b) = a) ψ_(h−1)(a', l − 1) π(b)`.)

Conditionally on `H_0`, the rest of the argument of Lemma 2 is unchanged: the states `q(u_c)`, `c >= 1`,
and `q(t_(I+1)), ..., q(t_(K−1−d))` are i.i.d. `π` and independent of `t_0`'s leaves (disjoint bottom
leaves), the tail is an independent i.i.d. `θ_H` block of the right length, and on the comparison side
the same holds with `t_1, ..., t_(K−1)` and an independent `ψ_(H'_0)` first coordinate. So, given `N = n`
on one side and `N = n + d` on the other, the two laws of `Ξ⁺` are

`(1/(L''+1)) Σ_(h=H)^(H+L'') ψ_(h−j_0) ⊗ Λ`   and   `(1/(L''+1)) Σ_(h=H)^(H+L'') ψ_h ⊗ Λ`,

with the same `Λ` (the i.i.d. `π` states of the other `K − 1` prefix positions, and the tail). Two
uniform mixtures of the same family over index sets that differ by a shift of `j_0` are within total
variation `j_0 / (L'' + 1) <= D / (L'' + 1)`; tensoring with a common `Λ` does not change that. Mixing
over `N` as in Theorem C adds `2 d / R_L`, so

`|| Ξ⁺_* ρ^μ_s − Ξ⁺_* μ || <= 2 D / R_L + 2 D / (L'' + 1) → 0`,

and Corollary A.2 gives `δ_1(Ξ⁺) = 0`. ∎

The exact mixture distances are tabulated in Stage 5 of `output.txt`: `j / (L'' + 1)` for `j = 1, 2, 3`
and `L'' + 1 ∈ {2, 4, 8, 16, 32}`, always meeting the bound.

The germ at `1` needs no separate argument: it is the depth of the rightmost leaf of `t_(N_y−1)`, and
`N_y − 1 >= K` on the model, so `Ξ` reads that tree exactly.

## 5. Why the total caret count cannot be added here

In the model of Section 2 the exact tail determines the carets of every tree from position `K` on, so
reading `|y|` is the same as reading the carets of the first `K` trees. By Lemma 1 the first-`K` caret
sums are

`Σ_(c <= I+d) |u_c| + Σ_(a=I+1)^(K−1−d) |t_a| = Σ_(a=0)^(K−1−d) |t_a| − d`   versus   `Σ_(a=0)^(K−1) |t'_a|`,

a sum of `K − d` i.i.d. tower sizes shifted by `−d` against a sum of `K` i.i.d. tower sizes. The two
differ by `d` independent summands, not by a bounded shift, so no reweighting of the tower law and no
padding placed inside the prefix closes the gap while the tail is read exactly; and any padding placed
in the tail — the right comb of Theorem B of the gate, whose length is the free coordinate there — is
itself read exactly and so carries no freedom. Stage 4 measures the residue: `3885/4096` for
`(Ξ, |y|)`. This is a limitation of the model, not a proof that `(Ξ, |y|)` has positive defect; by
Corollary A.3 of the gate a positive defect there would prove `thompson-f-is-not-amenable`.

## 6. What survives

Writing `π_K(y) = (t_0, ..., t_(K−1))`, Lemma 1 makes `(X_K, {σ_s})` a partial-action system and
`M → X_K` a skew product over the tail. Theorem C says the tail direction is inert **above any reading
of the base by an invariant with an idempotent state measure** — and only above such a reading, since
that measure is what Lemma 4.2 needs in the proof of Lemma 2. (An earlier version of this section said
"the residue is therefore exactly the base"; that does not follow, and the 2026-09-17 referee refuted
the claim node on exactly this step — event `31e58aeb`.) The residue is:

- `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead`: the same statement for
  invariants with no idempotent state measure — prefix depths, prefix sizes, exact prefix shapes. These
  are coarsenings of no `Ξ_(K,Q)` reached by Theorem C, so Lemma A.4 does not deliver them, and
  `Ψ(y) = ((depth t_0, ..., depth t_(K−1)), (t_K, t_(K+1), ...))` is untouched by everything proved
  here. Until this is settled, "a certificate must read the exact shapes of the first `K` trees" is not
  a consequence of Theorem C.
- `thompson-f-prefix-observation-shadow-defect`: is `δ_λ(π_K) > 0` for some `S` and some `λ > 1`?
  Positive answer proves `thompson-f-is-not-amenable` (Theorem A of the gate with Lemma 2.1(a) of the
  finite-state proof); `δ_1(π_K) = 0` for every `S` plus a transfer from `π_K` back to `id_M` would
  prove `thompson-f-is-amenable`.
- `(Ξ, |y|)`, Section 5 — one member of the first bullet's family, since with the tail exact `|y|` is
  the prefix caret sum.
- group-side flows on reduced pairs of forests, unchanged from the gate's Scope.
