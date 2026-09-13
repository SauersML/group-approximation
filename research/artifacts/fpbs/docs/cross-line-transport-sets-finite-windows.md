# Transport sets that read several fibre lines: finite windows, clumps, and a reduction

Lane `fixed-price-correlated-levels`, 2026-09-12. Supports
`fpbs-finite-window-twisted-levels-disconnected` (established) and the open claim
`fpbs-cross-line-correlated-transport-set-generates`, which stays OPEN.

## 0. Question and verdict

**Question.** Find a Borel `A ⊆ [0,1]^Gamma` of arbitrarily small measure whose open levels are
correlated across fibre lines, such that `Phi_A = {t} ∪ {s|_A : s in S}` generates the orbit
relation of the Bernoulli shift. Or prove a cross-line disconnection theorem that kills route
`fpbs-3-manifold-fixed-price-via-correlated-transport-sets`.

**Settled.**
- Theorem W (Section 2): if `A` depends only on the coordinates in a finite window `W ⊆ Gamma`,
  and `mu(A) < delta_0^D` with `D = |W^-1 W|`, then `Phi_A` does not generate. This covers every
  set that reads finitely many coordinates, on any number of lines.
- Lemma R (Section 3): the open claim holds iff it holds with finite-window sets. So small
  generating sets, if they exist, can be taken local. By Theorem W a local one of measure `delta`
  has a window with `D >= log(1/delta) / log(1/delta_0)`.

**Not settled.** The threshold of Theorem W depends on the window. Section 4 shows that clumped
sets open exponentially many paths together with one rare event. It gives examples for all three
candidates: Rokhlin-type bases, slice percolation clusters, and rare patterns in a ball. Their
charge per witness is at least `delta^(c/|W|)`, so the exponent `1/D` of Theorem W can improve at
best to order `1/|W|`. A per-witness first moment cannot give a uniform theorem. No construction
was found either. The open claim stays OPEN and the route is not invalidated.

## 1. Setting

- `Gamma = N semidirect_phi Z`, `t`, `S`, the hypotheses (H1), (H2), and the constants `K`,
  `c_K = 2^(K+2)` (called `A` there), `rho(delta) = 2^(K+3) |S|^2 sqrt(delta)` and `delta_0` are
  those of `research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md`,
  Sections 3 and 4. Here `S` also generates `N`, so `S ∪ {t}` generates `Gamma`.
- `mu` is the product measure on `[0,1]^Gamma`, with `(g.x)(h) = x(h g)`. The action is essentially
  free and ergodic.
- **Points.** `Gamma = <t> N` with `<t> ∩ N = {e}`, so `(u, m) -> t^m u` is a bijection
  `N x Z -> Gamma`. Put `omega_x(t^m u) = 1_A(t^m u . x)`. This is the field of item (1) of
  `fpbs-twisted-level-graph-generates-cyclic-extension`, and `T_omega` is its graph on `N`.
- In `Gamma` the open point `g = t^m u` joins the line `<t> g` to the line `<t> s g`, because
  `s t^m u = t^m phi^-m(s) u`. So `T_omega` is the quotient, by `<t>`-lines, of the graph on
  `Gamma` with all `t`-edges and the `S`-edges at open points.
- **Windows.** `A` is *`W`-local*, for a finite `W ⊆ Gamma`, if it is measurable with respect to
  `x|_W`. Then `omega_x(g)` depends only on `x|_(W g)`, since `(g.x)(w) = x(w g)`.
- `D(W) = |W^-1 W| <= |W|^2 - |W| + 1`.

## 2. Theorem W: finite windows

**Theorem W.** Let `A` be `W`-local with `delta = mu(A) < delta_0^D(W)`. Then
`P(e <-> s in T_omega) < 1` for every `s in S`, `T_omega` is almost surely disconnected, and
`Phi_A` does not generate.

**Proof.**

*Disjoint windows.*
- `W g ∩ W g' != ∅` iff `g' in W^-1 W g`, which allows at most `D` points `g'`, including `g`.
- So every finite `V ⊆ Gamma` contains `V'` with `|V'| >= |V| / D` whose windows are pairwise
  disjoint. To get it, pick `g in V`, delete `W^-1 W g ∩ V`, and repeat.
- The events `{omega(g) = 1}`, `g in V'`, depend on disjoint sets of coordinates, so they are
  independent under `mu`. Hence `P(omega = 1 on V) <= delta^(|V| / D)`.

*Steps 1 and 3 of main's proof* are deterministic and are used unchanged: witness sets of size at
most `2|S|`, and the path count `P_l(s) <= |S|^l 2^((K+2)(l+1))`.

*Step 2 for windows.* Let `gamma = (w_0, ..., w_l)` be self-avoiding.
- As in main's Step 2 there are at most `(2|S|)^l` choice functions `c`, and each has at least
  `l/2` distinct values.
- By disjoint windows, `P(all values of c open) <= delta^(l / (2D))`.
- So `P(gamma open) <= (2|S|)^l delta^(l / (2D))`.

*Step 4 for windows.* Main's sum with `sqrt(delta)` replaced by
`delta^(1/(2D)) = (delta^(1/D))^(1/2)` gives `P(e <-> s) <= c_K sum_(l>=1) rho(delta^(1/D))^l`.
Since `delta^(1/D) < delta_0` and `rho` is increasing, `c_K rho / (1 - rho) < 1`.

*Almost sure disconnection.*
- The set of `x` whose `Phi_A`-class is the whole orbit `Gamma x` is `Gamma`-invariant. By
  ergodicity it has measure 0 or 1.
- By the dictionary of Section 1 and freeness, it is the event that `T_(omega_x)` is connected. That event has
  probability at most `P(e <-> s) < 1`, so its measure is 0. ∎

**What it covers.** Every `W`-local set below its threshold, whichever lines it reads. That
includes Rokhlin-type bases, rare patterns and thinned percolation read in a bounded radius. It
does not cover sets that are not local, such as those reading whole lines `x|_(<t> F)`. By
Lemma R the open claim reduces to local sets anyway.

## 3. Lemma R: reduction to finite windows

For Borel `A`, `r >= 1` and `s in S`, let `E_s^r(A)` be the set of `x` such that no path of at most
`r` edges of `Phi_A` joins `x` to `s x`. Let `B_r` be the ball of radius `r` in `Gamma` for
`S ∪ {t, t^-1}`.

**Lemma R.** The following are equivalent.
- (a) For every `epsilon > 0` there is a Borel `A` with `mu(A) < epsilon` such that `Phi_A`
  generates. This is the open claim.
- (b) For every `epsilon > 0` there are a finite `W` and a `W`-local `A` with `mu(A) < epsilon`
  such that `Phi_A` generates.
- (c) For every `epsilon > 0` there are `r` and a Borel `A` with
  `mu(A) + sum_(s in S) mu(E_s^r(A)) < epsilon`.

**Proof.**
- (b) ⇒ (a) is trivial.
- (a) ⇒ (c): take `A` from (a) with `mu(A) < epsilon / 2`. For almost every `x` a finite path of
  `Phi_A` joins `x` to `s x`, so `E_s^r(A)` decreases to a null set as `r -> ∞`. Choose `r` with
  `sum_s mu(E_s^r(A)) < epsilon / 2`.
- (c) ⇒ (a) and (c) ⇒ (b) follow from the next two steps.
- *Patching.* Let `A' = A ∪ ∪_(s in S) E_s^r(A)`. Then `Phi_A'` generates:
  - for each `x` and `s`, either `x in E_s^r(A) ⊆ A'`, so `s|_A'` joins `x` to `s x`, or a path of
    `Phi_A ⊆ Phi_A'` does;
  - `t`-edges are always present, and `S ∪ {t}` generates `Gamma`.
- *Localizing.*
  - Whether `x in E_s^r(A)` is a Boolean function of `(1_A(gamma x))_(gamma in B_r)`.
  - Choose a `W_1`-local `A_1` with `mu(A Δ A_1) < eta`. The two Boolean functions agree off
    `∪_(gamma in B_r) gamma^-1 (A Δ A_1)`, which has measure at most `|B_r| eta`.
  - So `mu(A_1) + sum_s mu(E_s^r(A_1)) < epsilon + (1 + |S| |B_r|) eta`.
  - Each `E_s^r(A_1)` is `W_1 B_r`-local, so patching `A_1` gives a `W_1 B_r`-local generating
    set of measure below `epsilon + (1 + |S| |B_r|) eta`. With `eta` small this is (c) ⇒ (b). ∎

**Corollary.**
- If the open claim holds, then for every `epsilon` there is a local generating set of measure
  below `epsilon`.
- By Theorem W, every `W`-local generating `A` has `D(W) >= log(1/mu(A)) / log(1/delta_0)`, so
  `|W| >= (log(1/mu(A)) / log(1/delta_0))^(1/2)`.
- A theorem killing the route must therefore give one `epsilon_0 > 0` such that no local `A` with
  `mu(A) < epsilon_0` generates, whatever the window. Theorem W gives `epsilon_0` only as a
  function of the window.

## 4. The per-line charge fails for clumped sets

**4.1 Clumps.**
- Let `Q ⊆ Gamma` be finite, `P ⊆ [0,1]^Q` Borel with probability `p > 0`, and
  `C(x) = {h in Gamma : (x(q h))_(q in Q) in P}`.
- For a finite `K ⊆ Gamma` put `A_K = {x : e in K C(x)}`. Then `A_K` is `Q K^-1`-local and
  `mu(A_K) <= |K| p`.
- Since `C(g.x) = C(x) g^-1`, the open set of `x` is `K C(x)`.
- So one occurrence `h in C(x)`, of probability `p`, opens all of `K h` at once.

**4.2 Slice clumps open exponentially many paths together.**
- Take `K = D ⊆ N` with `e in D`, connected in `Cay(N, S)`. For `h = t^a u`, the points
  `d h = t^a phi^-a(d) u` are the pairs `(phi^-a(d) u, a)`, all at level `a`.
- If `d_0, ..., d_l` is a self-avoiding path in `D` with `d_i = s_i d_(i-1)`, put
  `w_i = phi^-a(d_i) u`. The open pair `(w_(i-1), a)` gives the edge
  `{w_(i-1), phi^-a(s_i) w_(i-1)} = {w_(i-1), w_i}`.
- So when `h in C(x)`, every self-avoiding `S`-path inside `D` is an open path of `T_omega` at
  level `a`. For `D` a ball of radius `R` there are exponentially many such paths of each length
  `l <= R`, and each is open with probability at least `p`.
- The (LI) charge bounds one choice function by `delta^(l/2)`, with `delta <= |D| p`. The choice
  `c(i) = (w_(i-1), a)` has all its values open with probability at least `p`. For `l >= 3` and
  `p < |D|^-3`, `delta^(l/2) <= (|D| p)^(3/2) < p`, so that charge fails. The whole bound
  `(2|S|)^l delta^(l/2)` fails too once `p < (2|S|)^-6 |D|^-3`.

This is the quotient-split mechanism of `fpbs-quotient-split-actions-have-cost-one`, localized: a
whole fibre word is paid for by one rare event.

**4.3 The exponent of Theorem W is of the right order.**
- Take `D` a geodesic segment of length `R` through `e`, with `l = R`. Then `W = Q D^-1` has
  `|W| <= |Q| (R + 1)` and `delta <= (R + 1) p`.
- The charge per step of the open segment is `P(gamma open)^(1/l) >= p^(1/R) >=
  (R+1)^(-1/R) delta^(1/R)`. Since `|W| <= 2|Q| R`, this is at least
  `(R+1)^(-1/R) delta^(2|Q| / |W|)`.
- So a per-witness first moment cannot beat thresholds exponentially small in `|W|`. The exponent
  `1/D` of Theorem W can improve at best to order `1/|W|`.

**4.4 The three candidates.**
1. **Rokhlin-type bases of the whole `t`-action**, meaning `A ∩ t^i A = ∅` for `0 < |i| < L`.
   - The condition restricts rows only. A slice clump meets each `<t>`-line at most once, since
     `N ∩ t^i N = ∅` for `i != 0`.
   - Thin locally: keep `h in C(x)` iff `C(x) ∩ D^-1 t^i D h = ∅` for all `0 < |i| < L`. If
     `d h = t^i d' h'` with both kept, then `h' in D^-1 t^-i D h`, which contradicts keeping `h`.
     So `{x : e in D C'(x)}` is local and satisfies the Rokhlin condition.
   - Take `P = {y : y(q) < eta for all q in Q}`, so `p = eta^|Q|`. For `h' != h`, `Q h' != Q h`
     because `Gamma` is torsion-free, so `P(h, h' in C) <= p eta`. Hence
     `P(e in C'(x)) >= p (1 - 2L |D|^2 eta) > 0` for small `eta`.
   - 4.2 applies with `p` replaced by `P(e in C'(x))`. The charge fails. The Rokhlin property adds
     no connecting mechanism.
2. **A factor mixing for `N` but correlated across lines: slice percolation clusters.**
   - Read independent bond variables `xi` with parameter `p_b` on the edges `{g, s g}` from
     digits of `x(g)`, orienting each pair `{s, s^-1}` once.
   - Each `xi`-cluster lies in one slice `t^a N`, since `s t^a u = t^a phi^-a(s) u`. The slice
     graph is `Cay(N, phi^-a(S)) ≅ Cay(N, S)`.
   - Take `p_b < 1/(|S| - 1)`. The expected number of open self-avoiding paths of length `n` is at
     most `|S| (|S|-1)^(n-1) p_b^n -> 0`, so clusters are finite almost surely.
   - Let `A_k = {x : the xi-cluster of e has at least k vertices}`. This is local, and
     `delta_k = mu(A_k) -> 0`.
   - The open set is `{g : |C_xi(g)| >= k}`. For a self-avoiding `S`-path of length `l` in a
     slice, all its witness points lie in one cluster when its edges are `xi`-open. Harris–FKG
     gives `P(gamma open) >= p_b^l delta_k`.
   - The charge per step is `p_b`, independent of `k`. The (LI) bound `(2|S|)^l delta_k^(l/2)` is
     violated for fixed `l >= 3` and large `k`.
3. **Rare patterns in a ball, possibly repeated along `phi`-orbits.**
   - Let `A = {x : C(x) ∩ B_R != ∅}`, with `B_R` the ball of radius `R` in `Gamma` for
     `S ∪ {t, t^-1}`. Since `B_R` is symmetric, `A = A_(B_R)` and its open set is `B_R C(x)`.
   - The shape `Q` is arbitrary. For example, `Q = ∪_(|j| <= J) t^j Q_0` with `Q_0 ⊆ N` reads the
     rows `phi^-a(Q_0) u` at the levels `a+j`, since `t^j q t^a u = t^(a+j) phi^-a(q) u`. That is a
     pattern repeated along a `phi`-orbit.
   - `B_R` contains the ball `D` of radius `R` in `Cay(N, S)`. So one occurrence opens `D h`, and
     4.2 applies whatever `Q` is. For `d` in the ball of radius `R - J`, the same occurrence also
     opens the rows `phi^-a(d) u` at the levels `a+j`, `|j| <= J`.

**4.5 A clump-level count (heuristic, not a claim).**
- Charge occurrences instead of witnesses. Two slice clumps `D h`, `D h'` share a line only if
  `h' in D'^-1 <t> D' h`, where `D' = D ∪ S D`.
- Bounded excursion leaves at most `const |D|^2` candidates, so the expected number of linked clumps
  is at most `const |D|^2 p ≈ const delta |D|`.
- A clump-level first moment might give disconnection when `delta |D|` is small. It says nothing
  when `|D| >> 1/delta`. Clumps much larger than `1/delta` are what remain.

## 5. Status

- **ESTABLISHED:** `fpbs-finite-window-twisted-levels-disconnected` (Theorem W, Lemma R and the
  corollary).
- **OPEN:** `fpbs-cross-line-correlated-transport-set-generates`. The route
  `fpbs-3-manifold-fixed-price-via-correlated-transport-sets` is not invalidated.
- **A uniform disconnection theorem** would need to charge occurrences, not witnesses. It must give
  one bound for all local `A` with `mu(A) < epsilon_0`.
- **A construction** needs a local `A` with `D(W) >= log(1/delta) / log(1/delta_0)`. By 4.5 it
  plausibly also needs clumps of size well above `1/delta`.
- **Not treated here:** normal-subgroup criteria (lane `fp-normal-subgroup-criterion`) and Kazhdan
  groups (lane `fp-kazhdan-either-way`).
