---
rg: 2
id: ownership-subshifts-conserve-shell-waste
kind: claim
title: Ownership and arrow shifts conserve shell waste, so the full ones are never strongly irreducible
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that asks whether a strongly irreducible proper SFT domain can carry a strongly post-surjective, non-pre-injective map; this proves that the ownership and arrow SFTs, the natural domains for such maps, are not strongly irreducible, and says what a strongly irreducible subshift of them must look like.
  nonamenable-groups-carry-arrow-shift-strict-automata: that builds the arrow shifts and their strict hotel maps; this proves those arrow shifts are not strongly irreducible once some point has an indegree of three or more, which holds for every S^2 with X_S nonempty.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that excludes domains with a finite orbit or a constant point, with no irreducibility; this is a conservation law that rules out strong irreducibility for domains that have no finite orbit at all.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is about domains with a constant point; ownership and arrow shifts have no finite orbit, so that result does not reach them, while this one does.
artifacts:
  - experiments/ownership-sft-si-2026-09-17/shell_waste_check.py
  - experiments/ownership-sft-si-2026-09-17/shell_waste_check.out
  - experiments/ownership-sft-si-2026-09-17/perfect_branch_probe.py
  - experiments/ownership-sft-si-2026-09-17/perfect_branch_probe.out
---

**ESTABLISHED** by `ownership-subshifts-conserve-shell-waste-proof` (elementary: a counting identity, the
Mendelsohn–Dulmage matching theorem, and one gluing).

**Setting.**
- `G` is a countable group acting by `(g.x)(h) = x(g^(-1) h)`. `S ⊆ G` is finite, and `k ≥ 1`.
- The **ownership shift** `Own(S,k)` is the set of `o = (s_1, ..., s_k) : G -> S^k` for which
  `(g, i) -> g s_i(g)` is injective on `G × [k]`. The **claims** of `g` are the `g s_i(g)`. A vertex is
  **unclaimed** if it is not a claim, and `o` is **perfect** if no vertex is unclaimed.
- For `e ∈ S = S^(-1)`, the **arrow shift** is `X_S = {φ ∈ S^G : every h has at least two g with g φ(g) = h}`,
  as in `nonamenable-groups-carry-arrow-shift-strict-automata`. `φ` is **exact** if every indegree is 2.
- A subshift `Y` is **strongly irreducible** (SI) with finite `K ∋ e` if, for all `x_1, x_2 ∈ Y` and finite
  `E_1, E_2 ⊆ G` with `E_1 K ∩ E_2 = ∅`, some `y ∈ Y` agrees with `x_1` on `E_1` and with `x_2` on `E_2`.

**Theorem.**
1. **Shell-waste identity.** Let `Q` be finite, `T ⊇ QS`, and `W ⊇ T S^(-1) \ Q` with `W ∩ Q = ∅`. For
   `o ∈ Own(S,k)`, the number of unclaimed vertices of `T` is
   `u_o(T) = |T| - k|Q| - #{(w,i) : w ∈ W, w s_i(w) ∈ T}`.
   For `φ ∈ X_S`, the excess `e_φ(T) = Σ_{t ∈ T} (indeg_φ(t) - 2)` is
   `e_φ(T) = |Q| + #{w ∈ W : w φ(w) ∈ T} - 2|T|`.
   Both depend only on the restriction of the point to `W`.
2. **Dichotomy.** Let `Y ⊆ Own(S,k)` be a nonempty SI subshift with constant `K`. Put
   `V = S ∪ S^(-1) ∪ K ∪ K^(-1) ∪ {e}`. Then one of the following holds.
   - Every point of `Y` is perfect.
   - Every point of `Y` has an unclaimed vertex in every set `g V^3`.

   The same holds for an SI `Y ⊆ X_S`: either every point is exact, or every point has a vertex of indegree
   at least 3 in every `g V^3`.
3. **The full shifts are not SI.**
   - If `e ∈ S` and `Own(S,k+1)` is nonempty, then `Own(S,k)` is not SI.
   - If `X_S` contains a point with some indegree at least 3, then `X_S` is not SI.
   - If `X_S` is nonempty, then `X_{S^2}` is not SI. So on every nonamenable group, every arrow shift `X_S`
     with `S ⊇ S_0^2` for some `S_0` with `X_{S_0}` nonempty fails to be SI.
4. **Free group instances.** On `F_2 = <a, b>` with `S = B_1 = {e, a^(±1), b^(±1)}`:
   - `Own(B_1, 2)` is not SI. Every vertex claiming three children away from `e` is a point of `Own(B_1, 3)`.
   - `X_{B_1}` is not SI. Every vertex points to its parent and `e` points to itself; non-root indegrees are 3.
5. **No finite orbits.** For `k ≥ 2` no point of `Own(S,k)` has a finite orbit.
6. **Factors.** If `X` is SI and `π : X -> Own(S,k)` is a factor map, then `π(X)` is SI. So item 2 applies
   to `π(X)`: every point of `π(X)` is perfect, or every point has unclaimed vertices syndetically. The same
   holds for factors onto subshifts of `X_S`.

**What it does to the dual-failure program.**
- The domains built from "each vertex owns `k` exclusive neighbours" are exactly the relaxed arrow and
  branching SFTs. These are the shapes whose strongly post-surjective, non-pre-injective maps onto full
  shifts were known. None of the full ones is SI, since each carries both a perfect point and a wasteful
  one, and waste is a conserved quantity on shells.
- An SI domain of this kind must pick one side. It is either **all-perfect**, where waste is forbidden and
  a local defect can never be absorbed, or **syndetically wasteful**, where every point wastes at bounded
  gaps.
- For an SFT on a free group, by item 5, either option is an SI SFT without periodic points. Poirier and
  Salo (arXiv 2401.16774, after Question 6.16) write verbatim: "We suspect that even strong irreducible
  SFTs have periodic points (and thus dense periodic points [9]) on free groups, but we do not have a
  proof."

**Computation.** `experiments/ownership-sft-si-2026-09-17/shell_waste_check.py` checks the free-group case
for `n = 2..6`, and its output is in `shell_waste_check.out`.
- It checks the explicit perfect point of `Own(B_1,2)`.
- It checks the identity with zero waste.
- It checks that the "away from `e`" centre pattern, with the perfect shell, has no completion. The
  matching deficiency is 1 at every `n`, while the control centre completes.

`perfect_branch_probe.py` is exploratory only. It shows that the all-perfect branch also fails to glue
translates of that perfect point, with deficiency histogram `{0: 42, 1: 101, 2: 18}` at `n = 5`. This is
not a proof that no SI all-perfect subshift exists.
