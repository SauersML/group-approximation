---
rg: 2
id: fpbs-gap-survives-product-generator-moves
kind: claim
title: Adding or removing one product generator never closes the percolation threshold gap
distinct_from:
  fpbs-nonuniqueness-phase-is-a-group-invariant: that compares arbitrary generating sets; this concerns one elementary move at a time, and with fpbs-generating-sets-connected-by-product-moves it is equivalent to that claim.
  fpbs-generating-set-threshold-comparison: that proves threshold inequalities with a power loss; this asserts the loss never closes a gap under a single move.
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

**OPEN.** Let `Gamma` be a finitely generated group, and let `S` be a finite
symmetric generating set not containing `e` with
`p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`. Then both kinds of move preserve the
gap:

- **Add.** For `t = uv` with `u, v in S` and `t ∉ S ∪ {e}`, the set
  `S ∪ {t, t^{-1}}` has `p_c < p_u`.
- **Remove.** For `t in S` with `t = uv`, `u, v in S \ {t, t^{-1}}`, the set
  `S \ {t, t^{-1}}` has `p_c < p_u`.

By `fpbs-generating-sets-connected-by-product-moves`, this implies Choi--Seo
Question 1.2 (`fpbs-nonuniqueness-phase-is-a-group-invariant`). Conversely, it
is a special case of that claim.

## Attempts

* **Threshold comparison with a power map.**
  `fpbs-generating-set-threshold-comparison` gives, for one Add move from `G` to
  `G⁺` (words of length `L = 2`, multiplicity `M`, map `phi`):
  - `phi(p_c(G)) <= p_c(G⁺) <= p_c(G)`;
  - `phi(p_u(G)) <= p_u(G⁺) <= p_u(G)`.

  So the gap survives whenever `p_c(G) < phi(p_u(G))`, which is about
  `p_c(G) < p_u(G)^2/4` in the generic case. Symmetrically, a Remove move keeps
  the gap whenever `phi^{-1}(p_c(G⁺)) < p_u(G⁺)`.

  **Where it dies:** when the two windows overlap. A counterexample must be an
  Add move that pushes `p_u` down to `p_c`, or a Remove move that pushes `p_c`
  up to `p_u`, inside those windows.
* **Lossless comparison through connection events.** Using `x <-> xt` in the
  old configuration as the comparison event for a new edge `{x, xt}` would lose
  nothing.

  **Where it dies:** those events are dependent across new edges. Turning a
  dependent comparison process into a threshold statement needs uniqueness
  monotonicity for that process, and the imports available on main give
  monotonicity only for Bernoulli percolation.
* **Relative gap along a subgroup** (`fpbs-relative-gap-along-any-subgroup-separates`).
  The comparison transfers finiteness of relative susceptibility only at the
  distorted parameter.

  **Where it dies:** same margin as above, since the criterion transfers from
  `G` to `G'` only if `p_c(G') < phi(p)`.
* **Margin class** (`fpbs-spectral-margin-survives-product-generator-moves`).
  - The margin `m(S) = 1 + h(S) - ||A_S||` certifies `p_c < p_u` when positive,
    and one move lowers it by at most 2.
  - So the claim holds at every `S` with `m(S) > 2`.
  - Such sets exist in every nonamenable group
    (`fpbs-large-margin-generating-sets-exist`).

  **Where it dies:** the certificate is perturbative and misses known gaps. The
  standard generators of `F_2` have a gap but `m = 3 - 2 sqrt(3) < 0`. A move
  from a gapped `S` with `m(S) <= 2` is not controlled.
* **Every complete proof proves the goal.** For each finitely generated
  `Gamma`, this claim restricted to `Gamma` is equivalent to: `Gamma` is
  amenable, or every generating set of `Gamma` has `p_c < p_u`.
  - **Gap ⇒ nonamenable.** A gap forces `Gamma` to be nonamenable, by
    `fpbs-hp-relative-burton-keane` with `H = Gamma`. So the goal implies the
    claim.
  - **Claim ⇒ goal.** `fpbs-large-margin-generating-sets-exist` and item 1 of
    `fpbs-spectral-margin-survives-product-generator-moves` give a gapped `S_0`
    in every nonamenable group, and
    `fpbs-generating-sets-connected-by-product-moves` joins `S_0` to any `S`.
    So the claim implies the goal.

  So this claim is equivalent to `fpbs-benjamini-schramm-universal`, group by
  group, and a counterexample to it would refute the goal.

  **Where it dies:** this is a reduction, not a proof. Arguments that use only
  the move structure and generic comparison, like the three above, cannot close
  the claim without proving the goal. The equivalence is recorded in prose
  only. A route from the goal to this claim would close a cycle through
  `fpbs-group-invariance-via-product-moves` and
  `fpbs-bs-via-generating-set-invariance`.
* **Two-parameter model along the new edges.** For an Add move, open the old
  edges with probability `p` and the new edges with probability `s`. The claim
  asks that the diagonal `s = p` still meets the nonuniqueness region.

  **Where it dies:** no import on main bounds how far the uniqueness threshold
  moves between `s = 0` and `s = p`. The only lower bound for `p_u` in use is
  `1/||A||`, and it gives exactly the margin class.
* **Remove half alone is equivalent to the goal; the Add half is redundant**
  (`fpbs-removal-descendants-of-gapped-sets`, swarm-0917). For a nonamenable
  `Gamma` and any `S`, there is a finite symmetric `T ⊇ S` with `e ∉ T`,
  `m(T) > K`, and a chain of Remove moves from `T` to `S`. To build `T`:
  - with `mu` uniform on `S`, let `W_l ⊆ W_{l-1}W_{l-1}` be the elements where
    `mu^{*2^l} >= rho^{2^l} e^{-(h-2eta)2^r}`;
  - add one dyadic band `V` of the typical level set of `mu^{*2^r}`;
  - remove the layers from the top down.

  The adjacency norms are bounded by `rho^n/threshold` through entrywise
  domination, and `|V| ~ e^{hk}` by Shannon–McMillan–Breiman (Lyons–Peres
  Theorem 14.10(ii), `fpbs-random-walk-shannon-and-avez-bounds`). So applying
  the Remove half along that chain already gives `p_c(S) < p_u(S)`. Two
  consequences:
  - Proof attempts need only ever handle Remove moves.
  - An Add-only chain from a gapped `S_0` reaches only supersets of `S_0`, so it
    cannot reach every `S`. For example, the standard basis of `F_2` has no
    proper generating subset. The mixed chain of
    `fpbs-generating-sets-connected-by-product-moves` is therefore replaced by a
    Remove-only chain.

  A counterexample `S` is the end of a Remove chain from a gapped superset `T`
  built from level sets of the walk on `S`, and exactly one step of that chain
  deletes a product pair and closes the gap.

  **Where it dies:** the margin of `T` is about `e^{(h-eta)k}/k`, but the chain
  has about `|T|/2 ~ e^{hk}` moves. The loss of 2 per move in
  `fpbs-spectral-margin-survives-product-generator-moves` item 3 is too large
  to carry the gap down to `S`. Whenever `m(S) <= 0`, as for the standard
  basis of `F_2`, any margin certificate must fail somewhere on the chain,
  whatever the per-move losses are. The final Remove steps therefore need a
  lower bound on `p_u` that is not spectral, and no import on main supplies
  one. This is a decomposition, not a proof.
* **Lossless two-path comparison, calibrated (2026-09-17, swarm-0917 w5)**
  (`fpbs-lossless-move-comparison-fails-marginal-transfer`). This sharpens the
  second attempt above. Open a new edge `{x, xt}` iff one of the `N`
  edge-disjoint `S`-paths `x -> xu_i -> xt` is open, with no splitting of old
  edges. The process has the same clusters as the old configuration, and its
  new-edge marginal is `m_N(p) = 1 - (1-p^2)^N`. A lossless argument would give
  `(LL) p_c(S) <= max(p_c(T), m_N^{-1}(p_c(T)))`.

  **Where it dies:**
  - **(LL) is false in general.** On `Z^2 -> ` triangular lattice (`N = 2`) it
    predicts `p_c(Z^2) <= 0.4383`. For `p ∈ (0.4383, 1/2)` the process has
    marginals above `p_c(tri) = 0.3473` but no infinite cluster (Kesten,
    Wierman). So marginals, invariance, finite-range dependence and monotonicity
    together do not transfer percolation.
  - **Even granted, (LL) keeps exponent 2.** Since `m_N <= N M^2 phi_M`, (LL)
    certifies a Remove step only when `p_c(T) < N p_u(T)^2`. It gains at most
    the constant factor `N M^2` over the power-map window, and it never reaches
    the residual band `N p_u(T)^2 <= p_c(T) <= p_u(T)` where a counterexample
    must live.

  So any proof of the Remove half through comparison of length-2 paths needs an
  input that is neither a marginal bound nor a threshold comparison. Whether
  (LL) holds on all nonamenable groups is untested beyond the tree-like `F_2`
  move, where it holds (`1/3 <= 0.4626`), and by the second point it would not
  decide this claim.
* **Superset uniqueness certificate refuted (minimal counterexample,
  2026-09-20, swarm-0917 w23)**
  (`fpbs-superset-pu-certificate-fails-on-237-triangle-group`, ESTABLISHED).

  Every threshold-comparison certificate above proves the Remove step through
  `(R*) p_c(T \ {t^±}) < p_u(T)` together with `p_u(S) >= p_u(T)`. `(R*)`
  along the Remove-only chain of `fpbs-removal-descendants-of-gapped-sets`
  would give the goal.

  `(R*)` is false. Take `Delta(2,3,7) = <x,y | x^2,y^3,(xy)^7>`,
  `S = {x, y^±}` and `T = S ∪ {(xy)^±}`, with `t = x·y`. Both graphs are
  planar, one-ended and nonamenable, so both are gapped by
  `fpbs-bs-planar-transitive-dual-threshold-identity` (BS Theorem 3.8, quoted
  from the paper body). The dual of `Cay(Delta,T)` has only 3-, 3- and 7-faces,
  so its non-backtracking root is `2.5424`. Hence
  `p_u(T) = 1 - p_c(T†) <= 0.60667`, while a detour-weighted walk count gives
  `p_c(S) >= p* = 0.63728`, the root of `2p^2(1+p-p^2) = 1`.

  **Where it dies:** the step `p_u(S) >= p_u(T)`. Here `p_u` jumps by more
  than `0.03` under one Remove move, and the old and new windows are disjoint.
  **Invariant:** the dual threshold `p_c(T†) = 1 - p_u(T)`, which rises when
  chords cut the large faces.

  The Remove half itself holds on this example. It is not refuted. Any proof of
  it must lower-bound `p_u(S)` intrinsically, through `S`'s own geometry or
  dual, and never through `p_u` of the gapped superset. This is the missing
  "non-spectral lower bound on `p_u`" of the Remove-chain decomposition, now
  shown not to be obtainable from `T`.

Details for the first three attempts are in Section 4 of
`research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md`. Details for
the last three are in Sections 4–7 of
`research/artifacts/fpbs-single-product-move-2026-09-12.md`.
