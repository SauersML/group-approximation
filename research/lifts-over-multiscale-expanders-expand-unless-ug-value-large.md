---
rg: 2
id: lifts-over-multiscale-expanders-expand-unless-ug-value-large
kind: claim
title: The label-extended graph of a q-label unique game has Phi(1/q) >= 1-nu unless val >= nu^3 tau^2/64, whenever the constraint graph satisfies e(A) <= eta mu(A) + gamma for mu(A) <= tau with 8 eta + 8 gamma q <= nu; conversely Phi_L(1/q) <= min(1 - val, Phi_H(1/q)), so lifts give no scale gain
distinct_from:
  small-set-expansion-hypothesis-implies-ugc: that is the published SSE-to-UG reduction; this is the opposite transfer, from UG on a multiscale-expanding base to SSE of its label-extended graph, by the identity map with explicit constants.
  galois-unique-game-value-is-transversal-expansion: that computes the value as transversal expansion of a Cayley lift; this controls the non-transversal sets of any lift (any permutations) through the base profile, and shows coset-union sets are the only other necessary test at density 1/q.
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills fibred compositions through sticky sets of the output graph; this is a transfer lemma, and its cylinder half extends that kill to label-extended outputs over sticky bases.
  spread-support-overlap-forces-non-expanding-small-sets: that finds non-expanding sets from spread support overlap of a view map; this decodes non-expanding sets of a lift into labelings and needs no support map.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that rounds YES instances of low label-extended threshold rank; this rounds NO-side non-expanding sets of the lift and needs no spectral hypothesis.
  elementary-abelian-galois-games-round-with-linear-loss: that rounds SDP certificates of symmetric F_p^N games; this rounds an integral set of the lift for arbitrary games, with no SDP.
artifacts:
  - experiments/ugc-sse-reframe-2026-09-17/check_lift_rounding.py
---

**ESTABLISHED.** Elementary and self-contained. Proof:
`lifts-over-multiscale-expanders-proof`. The exact replay of (1), (2) and (4)
over 75,456 sets is `experiments/ugc-sse-reframe-2026-09-17/check_lift_rounding.py`.

*Setting.* `H` is a regular multigraph on `V`, with uniform measure `mu`. A random
edge `(u,v)` is a uniform directed edge, so its law is symmetric. For
`A <= V` put `e(A) = Pr[u in A, v in A] = mu(A) (1 - Phi_H(A))`. A unique game
`U` on `H` has permutations `pi_uv` of `[q]` with `pi_vu = pi_uv^-1`. Its
label-extended graph `L` on `V x [q]` joins `(u,i)` to `(v, pi_uv(i))`.

For `S <= V x [q]` of measure `1/q`, the notation is:

- `l_v = |S_v|`, with `E l = 1`;
- `a_uv = |{i in S_u : pi_uv(i) in S_v}|`;
- `nu(S) = E[a_uv] = 1 - Phi_L(S)`;
- `R(S) = E[a_uv/(l_u l_v)]`, the expected value of the labeling that picks a
  uniform label of `S_v` at each vertex;
- `B_T = {l > T}` and `W_t = {l >= t}`.

1. **Master inequality.** For every `S` of measure `1/q` and every `T > 0`,
   `nu(S) <= T^2 R(S) + 2 int_0^T Pr[u in B_T, v in W_t] dt + 2 int_T^q e(W_t) dt`.
2. **Transfer.** Suppose `e(A) <= eta mu(A) + gamma` for every `A` with
   `mu(A) <= tau`, and `8 eta + 8 gamma q <= nu`. Then every `S` of measure `1/q`
   with `1 - Phi_L(S) >= nu` has `val(U) >= R(S) >= nu^3 tau^2 / 64`.
   *Scale form.* Let `|V| >= q`, `tau >= 2/q` and `eta <= nu/24`, and suppose
   `Phi_H(A) >= 1 - eta` for every `A` with `mu(A) in [1/q, tau]`. Then
   `val(U) < nu^3 tau^2/64` implies `Phi_L(1/q) >= 1 - nu`.
3. **Necessity.** `1 - Phi_L(1/q) >= val(U)`, witnessed by labeling sets. Also
   `1 - Phi_L(1/q) >= 1 - Phi_H(W)` for every `W` with `mu(W) = 1/q`, witnessed
   by the cylinder `W x [q]`. So a lift is `(1 - nu)`-expanding at density `1/q`
   only if the value is at most `nu` **and** the base is `(1 - nu)`-expanding at
   the same density. Permutation constraints cannot create expansion that the
   base lacks at scale `1/q`.
4. **Lift form of SSEH.** The map `U -> L(U)` is polynomial time and maps
   `val >= 1 - eps` to `Phi_L(1/q) <= eps`. By (2) it maps NO instances with
   (N1) `val < nu^3 tau^2/64` and (N2) `Phi_H >= 1 - nu/24` on scales
   `[1/q, tau]`, with `|V| >= q` and `tau >= 2/q`, to `Phi_L(1/q) >= 1 - nu`.
   For weighted graphs and SSEH's `[delta, 10 delta]` window, replace 64 by 640. Hence
   `small-set-expansion-hypothesis` follows from this statement: for every
   `nu > 0` there are `eps <= nu`, `tau` and `q` such that Gap-UG(`1 - eps`,
   `nu^3 tau^2/64`) is NP-hard on q-label instances whose constraint graph
   satisfies (N2).
   - By (3), N1 at level `nu` and N2 at scale `1/q` are forced on the NO
     outputs of every reduction that proves SSEH through label-extended graphs.
   - The converse, SSEH implies the lift form, is RST arXiv:1011.2586 Theorem
     3.2 (profile `Phi_G(S) >= Phi_(G(1-eps))(mu(S)) - gamma/mu(S)`, soundness
     `O(q^(-eps/(2-eps))) + gamma`). It also needs the standard fact that
     Gaussian noise-graph sets of measure `mu -> 0` have expansion `-> 1`, taken
     with `gamma <= nu/(48 q)`. That fact is cited, not re-derived here.
5. **Galois language.** For `Gal(G,K,mu)` the lift is `Cay(G,mu)` and the base
   is the Schreier graph on `G/K`. Labeling sets are transversals of `K`, and
   cylinders are unions of cosets of `K`. So `Cay(G,mu)` expands at density
   `1/k` only if both transversals and coset unions of density `1/k` expand.
   It does expand once transversals expand to value `< nu^3 tau^2/64` and coset
   unions expand at every density in `[1/k, tau]`.

**Consequence for gadget routes.** By (3), a label-extended output over a
constraint graph with a c-sticky ladder of step `varsigma'` has
`Phi_L(1/q) <= 1 - c + 2 varsigma' q`. The bound is the exact-volume step of
`sticky-cylinder-gadget-compositions-kill-proof`, applied to the base at
`delta = 1/q` and lifted to the cylinder. So running a fibred bounded-arity
composition and then twisting constraints does not escape the sticky kill.

**Bearing.** None of this proves or refutes `small-set-expansion-hypothesis`. It
splits the NO case of lift reductions into the value prerequisite N1 (a
`unique-games-conjecture`-type soundness) and the base-profile prerequisite N2
(expansion across scales `[1/q, tau]`), with every implication proved.

- Each can fail without the other.
  - Identity permutations on a multiscale expander satisfy N2 but have value 1.
  - `q` disjoint copies of any instance satisfying N1 still satisfy N1, since
    the value is unchanged. But one copy is a set of measure `1/q` with
    `Phi_H = 0`, which violates N2.
- (3) shows that neither can be dropped at scale `1/q`.
- The gap between the necessary scale `{1/q}` and the sufficient range
  `[1/q, tau]` is where a sharper characterization would live.

The idea of decoding a labeling from a non-expanding set of the label-extended
graph over a small-set expander is standard (Arora--Barak--Steurer style). The
statements and constants above were derived and replayed here, not copied from
a source.

DERIVATION lifts-over-multiscale-expanders-proof
