---
rg: 2
id: fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness-proof
kind: route
title: Read a spine off the critical Bernoulli cluster, push it along fixed words to any generating set, attach every other vertex by one arrow toward it, and squeeze the fixed-S cost between one and one plus d eps over two
target: fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness
requires:
  - fpbs-cost-is-limit-of-cayley-subgraphing-costs
  - fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost
  - fpbs-cluster-count-trichotomy
  - fpbs-critical-no-infinite-cluster
  - fpbs-central-z2-groups-have-fiid-sparse-spines
  - fpbs-fiid-spines-lift-via-infinite-conjugate-intersection
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-soft-collapse-over-conjugate-intersection-subgroups
  - fpbs-commensurated-subgroup-sparse-spines
  - fpbs-soft-collapse-on-wreath-and-split-extensions
---

Written derivation. `G = Cay(Gamma,S)` has edges `{g, gs}` for `s in S`, `Gamma` acts on the left, and `d = |S|`. The
last six requirements are used only for the members list.

**Step 0 (dictionary).** Let `b` be the Bernoulli shift on `X = [0,1]^Gamma`.
- Split each coordinate `x(h)` into independent uniforms `x(h)_0, x(h)_1, ...` by binary digits. Fix
  `S = S^+ ⊔ S^- ⊔ S^2`, where `S^- = (S^+)^-1` and `S^2` consists of the involutions.
- Label the vertex `h` by `x(h)_0`.
- Label the edge `{h, hs}`:
  - by `x(h)_(i(s))` if `s in S^+`;
  - by the fractional part of `x(h)_(i(s)) + x(hs)_(i(s))` if `s in S^2`. The `s`-edges form a perfect matching, so
    these labels are iid uniform.
- This gives a `Gamma`-equivariant map pushing the Bernoulli measure to the iid field on `V ⊔ E`. So every FIID object
  on `G` is a factor of `b`.
- By (H2) of `fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost` (proof, item 2), an a.s. connected spanning
  subgraph of `G` that is a factor of an action `a` is read at the root as a generating Borel subgraphing of
  `Phi_S^a`, with cost `(1/2) E deg(o)`. So:
  - an FIID connected spanning subgraph `omega` gives `C_sub^b(S) <= (1/2) E deg_omega(o)`;
  - an invariant one gives `c_inv(S) <= (1/2) E deg_omega(o)`.

**Step 1 (arrows).** Let `L` be an invariant, a.s. connected, infinite random subgraph of `G`, with
`P(o in V(L)) <= eps`.
- Let `(W_e)` be iid uniform labels independent of `L`. In the FIID case take them from an unused digit, so that
  everything stays FIID.
- Put `r(v) = dist_G(v, V(L))`. This is finite, because `V(L)` is nonempty and `G` is connected.
- For `v` not in `V(L)`, let the *arrow* `a(v)` be the edge `{v, vs}` with `r(vs) = r(v) - 1` that minimizes `W`. The
  minimum is unique a.s.
- Set `omega = L ∪ {a(v) : v not in V(L)}`. It is invariant (FIID if `L` is), and it is spanning.
- It is connected: following arrows from any `v` strictly decreases `r` and so reaches `V(L)`, and `L` is connected.
- Degree bound:
  - An `L`-edge at `o` forces `o in V(L)`, so `E deg_L(o) <= d eps`.
  - Every arrow leaves a vertex outside `V(L)`, so it is not an `L`-edge.
  - Two arrows never coincide, because `r` strictly decreases along each.
  - By the mass-transport principle, sending mass one from `v` to the head of `a(v)`, the expected number of arrows
    at `o` is `2 P(o not in V(L)) <= 2`.
- Hence `(1/2) E deg_omega(o) <= 1 + d eps / 2`.

**Step 2 (transport; Theorem 2).**
- Let `L` be a spine on `Cay(Gamma,S_0)`, and fix for each `s in S_0` a word `w_s` in `S` of length at most `K`.
- Let `L'` be the union, over the `L`-edges `{g, gs}`, of the `S`-paths `g, g w_s[1], g w_s[1..2], ..., gs`. Every
  vertex of `L` lies on some `L`-edge, since `L` is connected and infinite.
- `L'` is a deterministic equivariant function of `L`. It is connected and infinite, and it contains `V(L)`.
- If `o in V(L')`, then `{g, gs} in L` for some `s` and `0 <= j <= K`, with `g = (w_s[1..j])^-1`. So by invariance
  `P(o in V(L')) <= |S_0| (K+1) P(o in V(L)) <= |S_0| (K+1) eps`.
- Hence the kind of spine (FIID or invariant) passes to `S`, with constants depending only on `(S_0, S)`.

**Step 3 (Theorem 1).**
- *FIID.* Steps 1 and 0 give `C_sub^b(S) <= 1 + d eps / 2` for every `eps`, so `C_sub^b(S) <= 1`. The first bullet of
  the (H3) proof in `fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost-proof` gives
  `1 + beta_1 <= C(b) <= C_sub^b(S)`. Hence `beta_1 = 0` and `C_sub^b(S) = 1 = 1 + beta_1`.
  - By (H3), this is the hole at `S` and is equivalent to (P1) and (P2).
  - By (G) of `fpbs-cost-is-limit-of-cayley-subgraphing-costs`, it is also `lim_L m_S(P_L) = 0`.
- *Invariant.* Steps 1 and 0 give `c_inv(S) <= 1`. By (H2), `c_inv(S) = inf_a C_sub^a(S) >= inf_a C(a) = cost(Gamma)
  >= 1`, where cost at least one holds for any aperiodic relation, as in the same (H3) chain. So
  `c_inv(S) = cost(Gamma) = 1`.

**Step 4 (Theorem 3).** Suppose `p_c = p_u = p_c(G_0)` on `G_0 = Cay(Gamma,S_0)`, with `Gamma` nonamenable.
- `p_c < 1`, by the nonamenable bound `p_c <= 1/(1 + Phi)` of Benjamini–Schramm (1996), where `Phi > 0` is the edge
  Cheeger constant. So the interval `(p_u, 1)` is nonempty.
- For `p > p_u`, there is a.s. exactly one infinite cluster (`fpbs-cluster-count-trichotomy`).
- `theta(p) = lim_n P_p(o <-> boundary of B_n)` is a decreasing limit of polynomials, hence upper semicontinuous. It is
  nondecreasing, hence right-continuous. So `theta(p) -> theta(p_c) = 0` as `p` decreases to `p_c`
  (`fpbs-critical-no-infinite-cluster`).
- The unique infinite cluster of `{e : U_e <= p}` is an FIID connected infinite subgraph of density `theta(p)`. So
  `G_0` has FIID sparse spines.
- Step 2 moves them to every `S`, and Step 3 gives `C_sub^b(S) = 1`.

**Step 5 (Theorem 4).**
- A failure of the hole at `S` means `C_sub^b(S) != 1 + beta_1`. So `C_sub^b(S) > 1 + beta_1 >= 1` by the (H3) chain,
  and Step 4 in contrapositive gives `p_c < p_u` on every Cayley graph.
- If (P1) or (P2) fails at `S`, then so does the hole, by (H3).

**Members.** Apply Step 3 to the conventions of the listed spine nodes. Each of those nodes asserts spines on every
Cayley graph, and in any case Step 2 supplies that.

This is dependency bookkeeping over a written deduction, not a formal verification.
