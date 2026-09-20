---
rg: 2
id: gadgets-into-any-unique-games-stay-below-padding-line
kind: claim
title: Every per-gadget-certified reduction from 3Lin, kLin or any Latin-type predicate over an alphabet of size q into unique games over any alphabet L >= q with any permutation constraints has deficit ratio at most 2 - 1/N < 2 (N = |H|), so no such gadget crosses the padding line -- this closes the UG_q (q >= 5) and larger-alphabet survivors of the anchored-adversary kill
invalidates:
  - padding-line-via-local-gadgets-from-latin-predicates
distinct_from:
  three-lin-gadgets-stay-below-padding-line: that caps the same pipeline only for output permutation groups with at most two fixed points (Max-2Lin(Z_q), affine 2Lin, UG_3, UG_4, A_5) and leaves all of UG_q for q >= 5 open (its adversary gives 166/75 > 2 for S_5); this uses a different adversary (a fibre-plurality switch instead of anchor decoding), is blind to the permutation group, and covers every S_L with L >= q, at the price of the weaker uniform cap 2 - 1/N.
  unique-games-np-hard-below-the-padding-line: that is the open milestone R > 2; this kills one proof family for it and leaves it open.
  twin-mixture-caps-deficit-ratio-of-local-amplifiers: that caps maps whose input is already a unique game; this caps gadget reductions whose input is a 3Lin-type CSP.
  hadamard-gadget-deletion-ratio-window: that treats Hadamard predicates, whose information sets are small; they violate hypothesis (L1) here and stay a survivor.
artifacts:
  - experiments/ugc-fiber-switch-adversary-2026-09-17/check_fiber_switch_adversary.py
  - experiments/ugc-fiber-switch-adversary-2026-09-17/results-2026-09-20.txt
---

**ESTABLISHED (class kill).** Proof: `gadgets-into-any-unique-games-stay-below-padding-line-proof`.
It is elementary and imports nothing. The script checks the adversary with
exact rationals, exhaustively over all one-point edges for
`(q, L) = (2, 2), (2, 3), (2, 4), (3, 3)` and by search for larger cases.

## Setting

The setting is that of `three-lin-gadgets-stay-below-padding-line`, with two
changes. The output alphabet may be larger than the source alphabet, and the
output permutations are unrestricted.

* **Source.** `G` is a set of size `q >= 2`. `H ⊆ G^r` is the satisfying set
  of one source constraint, and `N = |H|`. There is a coordinate `j` with two
  properties:
  * (L1) the projection `H -> G^([r] \ {j})` is a bijection, so `N = q^(r-1)`;
  * (L2) for every `i != j`, the pair `(h_i, h_j)` is uniform on `G^2` when
    `h` is uniform on `H`.

  Examples:
  * 3Lin `u + v + w = b` over any abelian group of order `q`;
  * kLin for `k >= 3`;
  * any quasigroup equation `x ∘ y = z`.
* **Output.** A unique game over the alphabet `[L]`, with `L >= q`. The source
  alphabet is embedded in `[L]` by an injection `e`. The constraints are
  `z = γ(y)` with `γ` any permutation of `[L]`.
* **Gadgets.** A gadget is a finite distribution on output constraints over
  three kinds of variable:
  * the primaries `x_1, ..., x_r`, which carry `e(source value)`;
  * local auxiliary variables;
  * global reference variables with intended constant values.
* **Completeness.** `best(ξ)` is the least violated fraction with primaries
  `e(ξ)` and references at their intended values. The completeness is
  `c = max_(h ∈ H) best(h)`.
* **Certified soundness.** There are two certificates.
  * `s_cert = (1 - 1/q) min_(ξ ∉ H) best(ξ) + (1/q) min_(ξ ∈ H) best(ξ)`. This
    is the Trevisan--Sorkin--Sudan--Williamson case analysis against a source
    NO instance with value `1/q + eps`, the Håstad value for 3Lin.
  * `s_rand = E_(ξ uniform on G^r) best(ξ)`.

  We have `s_cert <= s_rand`.
* **Deficit ratio.** `R = s/c`, and the padding line is `R = 2`.

## Theorem

1. **Adversary.** Let `F_g = {h ∈ H : h_j = g}`. For `y : H -> [L]`, let the
   fibre-plurality score be
   `σ(y) = (1/N) sum_g max_a |{h ∈ F_g : y(h) = a}|`.
   Draw the following:
   * `ξ` uniform on `G^r`;
   * `t` uniform on `(1/q, 1)`;
   * `h*`, the point of `H` with `h*_(-j) = ξ_(-j)`;
   * `h'`: equal to `h*` if `ξ_j = h*_j`, and otherwise uniform in
     `F_(ξ_j)`.

   Put `A(y) = y(h')` if `σ(y) > t`, and `A(y) = y(h*)` otherwise. Then:
   * `A(γ ∘ y) = γ(A(y))` for every permutation `γ` of `[L]`;
   * `A` fixes the constant functions;
   * `A(e ∘ p_i) = e(ξ_i)` for every `i`, so it is random on the primaries;
   * for every pair `y, y'` differing at one point of `H`,
     `N Pr[A(y) != A(y')] <= 2 - 1/N`.
2. **Cap.** Every gadget in the setting has `s_cert <= s_rand <= (2 - 1/N) c`.
   So its certified deficit ratio is `R <= 2 - 1/N < 2`.
   * 3Lin over order `q`: `R <= 2 - 1/q^2`. That is `7/4`, `17/9`, `31/16`
     and `49/25` for `q = 2, 3, 4, 5`.
   * kLin: `R <= 2 - q^(1-k)`.
3. **Without (L2).** If only (L1) holds and `h_j` is uniform on `G`, put
   `σ_0 = max_(i != j) σ(e ∘ p_i) < 1`, and let `t` be uniform on `(σ_0, 1)`.
   Then `R <= 1 + (1 - 1/q)(1 - 1/N)/(1 - σ_0)`.

## Class kill, stated as invariant and step

* **Class.** Reductions of the following kind:
  * the source is a Gap-CSP(H) at soundness `1/q + eps`, with `H` satisfying
    (L1) and (L2);
  * each source constraint is replaced by a local gadget whose primaries are
    the source variables, encoded injectively into an output alphabet
    `L >= q`, with shared references allowed;
  * the output constraints are arbitrary unique-games constraints on `[L]`;
  * the NO case is certified per gadget, by `s_cert` or `s_rand`.

  Items 5 and 6 of `three-lin-gadgets-stay-below-padding-line` covered this
  class only for `L = q` and `Γ` with few fixed points.
* **Invariant.** The fibre-plurality score `σ` along the free coordinate `j`.
  * It is `1` on `p_j` and `1/q` on every other primary, by (L2).
  * It is `1/N`-Lipschitz for one-point changes.
  * It is invariant under every relabelling of `[L]`. That makes the bound blind
    to fixed points, which is where the anchored adversary broke.
* **Step where every member dies.** Soundness certification. The switch
  between reading `y` at `h*` and at `h'` costs at most
  `Pr[ξ_j != h*_j] (1/N)/(1 - 1/q) = 1/N` per edge. The two readings each cost
  `1/N`, and they overlap. So the adversary's deletion is at most
  `(2 - 1/N) c`, which is below the padding line `2c`.

## What this changes

* **Survivor 1 of `three-lin-gadgets-stay-below-padding-line` is dead.** That
  survivor was full `UG_q` for `q >= 5`, where the anchored adversary gave
  only `166/75` for `S_5` and `277/108` for `S_6`. Now 3Lin(Z_5) into `UG_5`
  has `R <= 49/25`.
* **Survivor 2 is dead too, when the primaries are source values in a larger
  alphabet.** Enlarging the output alphabet with injectively encoded primaries
  gives nothing.
* **The cap tends to 2 but never reaches it.** With `L2`, the bound tends to
  `2` as `N` grows, never above. The script finds it attained exactly once
  `L > q`. So for this class the padding line is the limit of per-gadget
  analysis, not an artefact of one adversary.
* **What remains.** Together with `ug-hardness-deficit-ratio-padding-line`,
  `twin-mixture-caps-deficit-ratio-of-local-amplifiers` and
  `hadamard-gadget-deletion-ratio-window`, the only local routes left for
  `R > 2` are the survivors below. Among them, Hadamard gadgets with `k >= 6`
  are the only per-gadget family from a random-threshold source.

## Survivors (not covered)

1. **Predicates without a co-dimension-one information set.** Examples are
   Hadamard / `RM(1,k)`-type predicates, where many coordinates lie outside
   every information set. These are handled only by
   `hadamard-gadget-deletion-ratio-window` (dead for `k <= 5`).
2. **Sources whose NO value is below the random threshold `1/q`.** Examples
   are label cover and d-to-1 games, where `(L2)` fails and `s_cert` weights
   `min_(ξ ∈ H)` by `delta << 1/q`. Item 3 alone does not settle them.
3. **Labels that are functions rather than encoded source values.** This is
   long-code or dictatorship-test composition, which is not a gadget.
4. **Global NO-side certificates** that are not per gadget, as in
   O'Donnell--Wright and the 2-to-2 proof.
