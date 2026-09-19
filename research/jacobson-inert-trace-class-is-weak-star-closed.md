---
rg: 2
id: jacobson-inert-trace-class-is-weak-star-closed
kind: claim
title: The inert trace class of the Jacobson mirror fibre product is weak*-closed, and hyperlinearity of EL_n(J) is a gap for one finitely supported element of C[P]
distinct_from:
  jacobson-mirror-exact-trace-part-is-multiplicative: that proves the inert class N is closed under products, mixtures, conjugation and ambient restriction, and leaves pointwise limits as the one open operation, closed only under the then-unimported hypothesis (SK); this proves unconditionally that tau -> tau^flat is weak*-continuous, so N is weak*-closed, and draws the finitary gap consequence.
  gl-infinity-f2-trace-simplex-is-extended-naturals: that computes the trace simplex of L = GL(infinity,2) and the CE semigroup S of EL_n(J); this transports the simplex to the mirror kernel L_- of P, reads the mirror-exact mass as the weight of the isolated point 0 of the extended naturals, and proves uniform convergence of the mirror averages over all traces of P.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that proves one CE character of E seeing L forces hyperlinearity; this turns that all-or-nothing statement into a quantitative gap for the CE value of one explicit self-adjoint element of the group algebra of the LEF group P.
  jacobson-mirror-head-swap-kills-ambient-approximations: that kills overgroup approximations trivial on L_-, at the head; this kills all weak*-limits of the inert operations, including limits of traces of exact finite-dimensional representations.
artifacts:
  - research/jacobson-inert-trace-class-weak-star-closed-proof.md
---

**ESTABLISHED** ([[jacobson-inert-trace-class-weak-star-closed-proof]]).

**Notation.** As in `jacobson-mirror-exact-trace-part-is-multiplicative`.
- `E = EL_n(J)` with `n >= 3`, and `P = E_+ x_(SL_n(A)) E_- <= H_bi` (LEF), with `E = P/L_-` via `q : P -> E`.
- `L_+ = GL_fin(V_+) x {1}` and `L_- = {1} x GL_fin(V_-)`, normal in `P`. The head is `w = (x_13(Q),1) in L_+`.
- `S_j = {-j,...,-1} x {1..n}` and `F_j = GL(span{e_s : s in S_j}) ≅ GL_(nj)(F_2) <= L_-`.
- `Tr(P)` is the set of traces of `P` (normalized, positive definite, conjugation invariant), with the pointwise
  (weak*) topology. `CE(P) ⊆ Tr(P)` is the compact convex set of Connes-embeddable traces.
- `tau^flat` and `m(tau) = tau^flat(1)` are as in (MX1). `N = {tau in Tr(P) : tau^flat constant on L_+}`.

**Theorem.**
1. **(Uniform mirror averages.)** Put `eps(M) = 12 * 2^(-M)`. For every trace `tau` of `P`, every `g in P` and
   every `j` with `nj >= 2`,

   ```text
   0 <= avg_(y in F_j) tau(y) - m(tau) <= eps(nj),
   |avg_(y in F_j) tau(y g) - tau^flat(g)| <= eps(nj)^(1/2).                              (U)
   ```

2. **(Mirror mass is the trivial weight.)** `tau|_(L_-) = sum_(k in N̄) mu_tau({k}) sigma_k`, with
   `mu_tau in Prob(N̄)`, and `m(tau) = mu_tau({0})`. Since `0` is isolated in `N̄`, `m` is weak*-continuous.
3. **(Continuity.)** For each `g in P`, the map `tau -> tau^flat(g)` is weak*-continuous on `Tr(P)`. Hence:
   - `N` is weak*-closed. It is a closed convex set, closed under products (MX3), conjugation and
     `L_+`/`L_-`-preserving automorphisms.
   - The **closed inert hull** lies in `N`. This is the smallest weak*-closed, convex, product-closed set of traces
     containing the following:
     - `delta_P`;
     - every trace with `m = 0`;
     - every trace of a finite-dimensional unitary representation of `P`;
     - every restriction `sigma|_P` of a trace `sigma` of an overgroup `G >= P` that contains the finitary site
       permutations (for example `H_bi`).
4. **(Gap for one element.)** Put

   ```text
   h_j = avg_(y in F_j) ( y - (y w + w y^(-1)) / 2 )  in C[P],   self-adjoint,
   delta(M) = eps(M) + eps(M)^(1/2),
   Gamma_j = sup_(tau in CE(P)) tau(h_j).
   ```

   Then for every `j` with `nj >= 2`, exactly one of the following holds:
   - `E` is hyperlinear and `Gamma_j >= 1`; the value `1` is attained at `delta_E o q`.
   - `E` is not hyperlinear and `Gamma_j <= delta(nj)`.

   `delta(M) < 1` as soon as `M >= 6`. So, for any single `j` with `nj >= 6`:

   ```text
   E hyperlinear   <=>   tau(h_j) > delta(nj) for some CE trace tau of P.
   ```

   For `n = 20` and `j = 1`, with `F_1 = GL_20(F_2)` on the sites `{-1} x {1..20}`, the threshold is
   `delta(20) < 0.0035`.

**What this does for the open hole.**
- **Closes the recorded survivor.** The only operation left open by the class-kill
  `jacobson-mirror-exact-trace-part-is-multiplicative` was the pointwise limit. It is closed unconditionally here.
  The Skudlarek list that closure needed is now imported (`gl-infinity-f2-extreme-characters-are-rank-powers`).
- **Kills the class.** Take any construction whose trace on `P` is a weak*-limit of traces built by products,
  mixtures, conjugations and automorphisms from the four generating families of Part 3. Every such trace is
  head-blind on its mirror-exact face. The class includes limits of traces of exact finite-dimensional
  representations of `P` and of any finitary-site overgroup; those are exactly the traces that the LEF structure of
  `P` and of `H_bi` supplies directly.
  - **Invariant.** The weak*-continuous multiplicative functional `tau -> tau^flat|_(L_+)`.
  - **Death step.** The uniform Burnside bound `avg_(GL_M(F_2)) sigma_k <= 12 * 2^(-M)` for `k >= 1`. It prevents
    any limit from creating mirror-exact mass that was not already present at finite level.
- **New decomposition (finitary gap).** Hyperlinearity of `EL_20(J)` becomes a single strict inequality
  `tau(h_1) > 0.0035` for a CE trace of the LEF group `P`.
  - A positive proof must produce matrix approximate representations of `P` that converge to a trace of `P` and
    satisfy it.
  - (U) forces the `F_1`-invariant subspace of any limit model to equal its `L_-`-invariant subspace, up to trace
    `12 * 2^(-20)`. So the head must move a macroscopic part of the `F_1`-invariants that is invariant under all of
    `L_-`, in the limit.
  - A negative proof has to show only `tau(h_1) <= 0.0035` for every CE trace of `P`. It does not need to show
    `tau^flat(w) = m(tau)` exactly: the gap turns an exact identity into a quantitative estimate with room
    `1 - 0.0035`.
- **Unchanged.** `agent-leavitt-not-bcs-negative-root-corner` and `non-hyperlinear-group` stay OPEN.

DERIVATION
jacobson-inert-trace-class-weak-star-closed-proof
