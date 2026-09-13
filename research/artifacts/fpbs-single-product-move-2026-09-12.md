# One generator move: a margin class, its reach, and why the full claim is Benjamini–Schramm

Lane `bs-single-product-move`, 2026-09-12. Target:
`fpbs-gap-survives-product-generator-moves` (OPEN), read against main
`9cb380bf4`. Sources re-read from PDFs fetched on MSI with curl and pulled with
`msi get`: Thom arXiv:1306.1767v1 (all 7 pages) and Juschenko–Nagnibeda
arXiv:1206.2183v3 (pages 1–4 and 12).

## 0. Results

1. **Margin class (proved, Sections 3–4).** For a finite symmetric generating
   set `S` of an infinite group with `e ∉ S`, put
   `m(S) = 1 + phi(S) - ||A_S||` (edge expansion, adjacency norm). Then
   `m(S) > 0` gives `p_c < p_u`, and adding or removing one symmetric pair of
   generators lowers `m` by at most 2. So `m(S) > 2k` keeps the gap through any
   `k` moves, and `m(S) > 2` proves the target at `S`.
2. **Reach (proved from Thom, Section 5).** Every nonamenable finitely generated
   group has simple generating sets of arbitrarily large margin.
3. **Obstruction (proved, Section 6).** Given 2 and
   `fpbs-generating-sets-connected-by-product-moves`, the target is equivalent to
   `fpbs-benjamini-schramm-universal`, also group by group. A full proof of the
   target is a proof of the goal, and a counterexample refutes the goal.
4. **Enhancement view (dead end, Section 7).**

Cairn nodes: `fpbs-spectral-margin-survives-product-generator-moves`,
`fpbs-thom-small-spectral-radius-generating-sets` and
`fpbs-large-margin-generating-sets-exist`, each with a proof or citation route.
Item 3 is recorded in the target's Attempts and is not wired, because its two
directions form a cycle through the goal.

## 1. Setting

- `Gamma` is an infinite finitely generated group, and `S` is a finite symmetric
  generating set with `e ∉ S`, `d = |S|`.
- `Cay(Gamma,S)` has an edge `{x, xs}` for `x ∈ Gamma` and `s ∈ S`. The edge
  `{x,y}` carries exactly the labels `x^{-1}y` and `y^{-1}x`, so the graph is
  simple and `d`-regular.
- `A_S f(x) = sum_{s ∈ S} f(xs)` on `l2(Gamma)`. Conjugating by `f ↦ f∘inv`
  turns it into `sum_{s ∈ S} lambda(s)`, so `||A_S|| = d rho(S)`, with `rho` as
  on JN p.2 and in Thom Section 1.
- `∂_E F` is the set of edges with exactly one endpoint in `F`, and
  `phi(S) = inf |∂_E F|/|F|` over finite nonempty `F`. This is `h(Y)` in
  `research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md` and
  `phi(Gamma,S)` on JN p.1.
- The **margin** is `m(S) = 1 + phi(S) - ||A_S||`.
- A **move** replaces `S` by `S+ = S ∪ {t, t^{-1}}` for some `t ∉ S ∪ {e}`, or
  by `S- = S \ {t, t^{-1}}` for some `t ∈ S` such that `S-` still generates. The
  target's product moves are moves.

## 2. Inputs

- **(E)** `fpbs-expansion-thinning-threshold`: an infinite connected locally
  finite graph of edge expansion `h > 0` has `p_c <= 1/(1+h)`.
- **(U)** `fpbs-cluster-count-trichotomy`, item 2: for every `p > p_u` the
  infinite cluster is unique almost surely.
- Harris–FKG for increasing events, and the monotone coupling between a graph
  and a spanning supergraph. Both are used inline on main, in steps 1 and 4 of
  `fpbs-expanding-factor-product-proof`.
- **(T)** Thom, *A remark about the spectral radius*, arXiv:1306.1767v1,
  Theorem 1 (p.2): "Let Γ be a finitely generated non-amenable group and Σ be a
  finite symmetric generating set. For every k ∈ N there exists a symmetric set
  S_k ⊂ Σ^k such that ρ(S_k) ≤ 4k · ln(|Σ|) · ρ(Σ)^k. Moreover, for every
  ε > 0, there exists a finite symmetric generating set S ⊂ Γ such that
  ρ(S) < ε."
  - Definitions (p.1): `m(S) := |S|^{-1} sum_{s ∈ S} s` and `ρ(S) := ||m(S)||`
    in the left-regular representation.
  - The theorem does not exclude `e ∈ S`.
  - Corollary 8 (p.5) states that some finite symmetric generating set has
    `p_c(Γ,S) < p_u(Γ,S)`. Its proof reads in full "Having Theorem 1 at hand,
    the proof proceeds as in [7]", where [7] is Pak–Smirnova-Nagnibeda.
- **(JN)** Juschenko–Nagnibeda, arXiv:1206.2183v3, p.3:
  - `p_c <= 1/(phi+1)`, credited to Benjamini–Schramm;
  - Theorem 2, `rho p_c |S| < 1` implies `p_c < p_u`;
  - Proposition 3, credited to Pak–Smirnova-Nagnibeda: `rho < 1/2` implies
    `p_c < p_u`.

  On p.4, from Definition 5 on, "generating set" means a simple one, and
  Question 6(1) asks whether every nonamenable group has generating sets with
  `rho -> 0`. Reference [19] on p.12 is Thom arXiv:1306.1767.

## 3. The gap criterion

**Lemma 3.1.** If `p ||A_S|| < 1`, then `tau_p(e, .) ∈ l2(Gamma)`.

*Proof.* If `g <-> e`, some path from `g` to `e` is open, and paths are walks.
So `tau_p(e,g) <= sum_{l >= 0} p^l A_S^l(g,e) = (sum_l p^l A_S^l delta_e)(g)`.
The series converges in operator norm, so the right side is in `l2`. ∎

**Lemma 3.2.** `p_u(S) >= 1/||A_S||`.

*Proof.*
1. Let `p > p_u`. Then `p > p_c`, so `theta(p) > 0`, and by (U) the infinite
   cluster is unique.
2. The events `{e <-> ∞}` and `{g <-> ∞}` are increasing. By Harris–FKG and
   uniqueness, `tau_p(e,g) >= P(e <-> ∞, g <-> ∞) >= theta(p)^2` for every `g`.
3. A function bounded below by a positive constant on an infinite set is not in
   `l2`. So Lemma 3.1 forces `p ||A_S|| >= 1`.
4. Let `p` decrease to `p_u`. ∎

These are steps 3–4 of `fpbs-expanding-factor-product-proof`
(`p_{2->2} >= 1/||A||` and `p_{2->2} <= p_u`).

**Lemma 3.3 (easy half of Mohar's inequality).** `phi(S) >= d - ||A_S||`.

*Proof.* For finite `F`,
`<A_S 1_F, 1_F> = sum_{x ∈ F} #{s ∈ S : xs ∈ F} = d|F| - |∂_E F|`. A boundary
edge `{x,y}` with `x ∈ F` is counted exactly once, by the pair `(x, x^{-1}y)`.
So `|∂_E F| >= (d - ||A_S||)|F|`. ∎

**Proposition 3.4.** If `m(S) > 0`, then
`p_c(S) <= 1/(1+phi(S)) < 1/||A_S|| <= p_u(S)`.

*Proof.* `||A_S delta_e||^2 = d`, so `||A_S|| >= sqrt(d) >= 1`, and `m(S) > 0`
forces `phi(S) > 0`. (E) gives the first inequality, `1 + phi(S) > ||A_S||` the
second, and Lemma 3.2 the third. ∎

**Corollary 3.5.** `m(S) >= 1 + d(1 - 2 rho(S))`, so `rho(S) < 1/2 + 1/(2d)`
gives `p_c < p_u`. This contains JN Proposition 3. Lemma 3.2 also gives JN
Theorem 2 directly: `p_c(S) ||A_S|| < 1` means `p_c < 1/||A_S|| <= p_u`.

## 4. A move changes the margin by at most 2

**Lemma 4.1.** Let `A` and `B` be bounded on `l2(Gamma)` with kernels
`0 <= B(x,y) <= A(x,y)`. Then `||B|| <= ||A||`.

*Proof.* `|<Bf,g>| <= <B|f|,|g|> <= <A|f|,|g|> <= ||A|| ||f|| ||g||`. ∎

**Proposition 4.2 (Add).** Let `t ∉ S ∪ {e}` and `S+ = S ∪ {t, t^{-1}}`.
1. `||A_{S+}|| <= ||A_S|| + 2`, and `+ 1` if `t^2 = e`.
2. `phi(S+) >= phi(S)` and `p_c(S+) <= p_c(S)`.
3. `m(S+) >= m(S) - 2`.
4. If `p_c(S) (||A_S|| + 2) < 1`, then `p_c(S+) < p_u(S+)`. This holds in
   particular when `m(S) > 2`.

*Proof.*
1. `S` is symmetric and `t ∉ S`, so `t^{-1} ∉ S`. Hence
   `A_{S+} = A_S + R(t) + R(t^{-1})`, or `A_S + R(t)` if `t^2 = e`, where
   `R(g)f(x) = f(xg)` is unitary.
2. `Cay(Gamma,S)` is a spanning subgraph of `Cay(Gamma,S+)`. Edge boundaries
   only grow, and percolation on the subgraph is dominated by percolation on the
   supergraph.
3. Combine 1 and 2.
4. By 2 and Lemma 3.2,
   `p_c(S+) <= p_c(S) < 1/(||A_S|| + 2) <= 1/||A_{S+}|| <= p_u(S+)`. If
   `m(S) > 2`, then `phi(S) > 0` and (E) gives
   `p_c(S) <= 1/(1+phi(S)) < 1/(||A_S|| + 2)`. ∎

**Proposition 4.3 (Remove).** Let `t ∈ S` with `S- = S \ {t, t^{-1}}`
generating `Gamma`.
1. `||A_{S-}|| <= ||A_S||`.
2. `phi(S-) >= phi(S) - 2`, and `- 1` if `t^2 = e`.
3. `m(S-) >= m(S) - 2`. So `m(S) > 2` gives `p_c(S-) < p_u(S-)`.

*Proof.*
1. Lemma 4.1, since `0 <= A_{S-} <= A_S` entrywise.
2. `Cay(Gamma,S-)` is `Cay(Gamma,S)` minus the edges `{x, xt}`. Count a removed
   boundary edge of `F` by its endpoint `x ∈ F`: it is `{x, xt}` or
   `{x, xt^{-1}}`, so there are at most `2|F|` of them (`|F|` if `t^2 = e`).
   Hence `|∂_E^{S-} F| >= |∂_E^S F| - 2|F|`.
3. Combine 1 and 2, then apply Proposition 3.4 to `S-`. ∎

**Theorem 4.4 (margin class).** Let `S_0, S_1, ..., S_k` be finite symmetric
generating sets without `e`, each obtained from the previous one by a move. If
`m(S_0) > 2k`, then `m(S_j) > 2(k-j)` and `p_c(S_j) < p_u(S_j)` for all `j`.
- With `k = 1`, every `S` with `m(S) > 2` satisfies the conclusion of the target.
- By Corollary 3.5, `rho(S_0) < 1/2 - (2k-1)/(2 d_0)` suffices.

*Proof.* Propositions 4.2 and 4.3 give `m(S_j) >= m(S_0) - 2j`. Then apply
Proposition 3.4. ∎

**Calibration.**
- **Free basis of `F_n`, `d = 2n`.** Here `phi = d - 2` and
  `||A|| = 2 sqrt(d-1)`, so `m = d - 1 - 2 sqrt(d-1)`. So `m > 0` exactly for
  `n >= 3`, and `m > 2` exactly for `n >= 5` (`F_5`: `m = 1 + 8 - 6 = 3`).
  These gaps are known independently, since free groups are hyperbolic
  (`fpbs-sc-choi-seo`); the example only calibrates the constant.
- **Standard generators of `F_2`.** `m = 3 - 2 sqrt(3) < 0`, so the certificate
  misses a known gap.
- **Corollary 3.5 is weaker on trees.** For the basis of `F_5` it gives
  `1 + 10(1 - 1.2) = -1`.

## 5. Reach: large margins in every nonamenable group

**Proposition 5.1.** Let `Gamma` be finitely generated and nonamenable, and let
`K > 0`. There is a finite symmetric generating set `S` with `e ∉ S` and
`m(S) > K`.

*Proof.*
1. Choose `epsilon ∈ (0, 1/4]` with `epsilon^{-2}/2 - 2 > K`. By (T) there is a
   finite symmetric generating set `S_0` with `rho(S_0) < epsilon`.
2. `rho(S_0)^2 = ||m(S_0)^2|| >= tau(m(S_0)^2) = 1/|S_0|`, because each `s` has
   exactly one partner `s' = s^{-1}` with `ss' = e`. So `|S_0| > epsilon^{-2}`.
   Thom p.4 records the same bound `rho(S) >= |S|^{-1/2}`.
3. Put `S = S_0 \ {e}`, which still generates. Then `A_S = A_{S_0} - I` if
   `e ∈ S_0`, so `||A_S|| <= epsilon |S_0| + 1`, and `|S| >= |S_0| - 1`.
4. By Lemma 3.3,
   `m(S) >= 1 + |S| - 2||A_S|| >= |S_0|(1 - 2 epsilon) - 2 >= |S_0|/2 - 2 > K`. ∎

**Corollary 5.2.** Every finitely generated nonamenable group has, for each `k`,
a simple generating set whose gap survives every sequence of `k` moves.

*Proof.* Proposition 5.1 with `K = 2k`, then Theorem 4.4. ∎

**Remarks.**
- Step 3 also gives `rho(S) <= (epsilon|S_0| + 1)/(|S_0| - 1) <= 2 epsilon`,
  because `epsilon|S_0| > 1/epsilon >= 4`. So the sets of (T) can be taken simple,
  which is the form JN Question 6(1) asks for.
- Proposition 5.1 with Proposition 3.4 proves
  `fpbs-simple-generating-set-with-gap-exists`. That node still says that small
  spectral radius for every nonamenable group "is open", which (T) contradicts.
  This lane did not edit that node or wire it.

## 6. Obstruction: the target is the Benjamini–Schramm conjecture

**Theorem 6.1.** Fix a finitely generated group `Gamma`. The following are
equivalent.
- **(a)** For every finite symmetric generating set `S` of `Gamma` with `e ∉ S`
  and `p_c(S) < p_u(S)`, every Add and every Remove product move keeps the gap.
  This is the target restricted to `Gamma`.
- **(b)** Either `Gamma` is amenable, or `p_c(S) < p_u(S)` for every finite
  symmetric generating set `S` of `Gamma` with `e ∉ S`.

*Proof.*
- **(b) ⇒ (a).** Suppose `S` has a gap. If `Gamma` were amenable,
  `fpbs-hp-relative-burton-keane` with `H = Gamma` would give
  `p_c(Gamma;G) = p_u(Gamma;G)`. For `H = Gamma` a `Gamma`-infinite cluster is
  just an infinite cluster, so that would say `p_c = p_u`. So `Gamma` is
  nonamenable, and (b) gives the gap on `S+` and `S-`, which are finite
  symmetric generating sets without `e`.
- **(a) ⇒ (b).** Let `Gamma` be nonamenable and `S` arbitrary.
  1. Proposition 5.1 gives `S_0` with `m(S_0) > 0`, so `S_0` has a gap by
     Proposition 3.4.
  2. `fpbs-generating-sets-connected-by-product-moves` joins `S_0` to `S` by
     finitely many product moves through finite symmetric generating sets
     without `e`.
  3. (a) carries the gap along the chain. ∎

**Consequences.**
- Over all groups, the target and `fpbs-benjamini-schramm-universal` are
  equivalent.
- For each nonamenable `Gamma`: (a) holds iff Choi–Seo Question 1.2 holds for
  `Gamma` iff the goal holds for `Gamma`. The second equivalence holds because
  `Gamma` has a gapped generating set (Propositions 5.1 and 3.4).
- The three Attempts already on the target (power-map windows, lossless
  connection events, relative gap) use only the move structure and generic
  comparison. None of them can succeed unless it also proves the goal.
- A counterexample to the target is a counterexample to the goal.
- This is recorded in prose only. On main, route
  `fpbs-group-invariance-via-product-moves` derives
  `fpbs-nonuniqueness-phase-is-a-group-invariant` from the target, and route
  `fpbs-bs-via-generating-set-invariance` derives the goal from that claim and
  `fpbs-simple-generating-set-with-gap-exists`. A route from the goal back to
  the target would close a cycle.

## 7. Enhancement view along the new edge orbit

Consider an Add move `S -> S+`. On `Cay(Gamma,S+)`, open `S`-edges with
probability `p` and the new `t`-edges with probability `s`. At `s = 0` this is
`Cay(Gamma,S)`, and on the diagonal `s = p` it is `Cay(Gamma,S+)`. The target
asks that the diagonal still meets the nonuniqueness region.

**Where it dies.**
- Strict decrease of `p_c` as `s` grows, the kind of statement essential
  enhancements give, does not help. What is needed is a bound on how far the
  uniqueness boundary moves between `s = 0` and `s = p`.
- No import on main bounds that movement. Main's uniqueness monotonicity (U) is
  for the one-parameter model.
- The only lower bound for `p_u` used on main is `p_u >= 1/||A||`. That bound
  moves by the additive 2 of Proposition 4.2, which is exactly the margin class.
- By Theorem 6.1, a quantitative control valid at every gapped `S` would prove
  the goal.
