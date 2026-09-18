# Constant-point domains: finite-quotient and sofic counts (2026-09-17)

Worker `swarm-0917-w8-w8-gs-last1`, wave 8, target `proper-sft-domains-admit-no-dual-failures`.

## 0. Conventions and the observation

Conventions as in `bounded-defect-domain-dual-failure-proof`.
- `(g⁻¹x)(w) = x(gw)`, `(hx)(g) = x(h⁻¹g)`. An automaton is `F(x)(g) = f((g⁻¹x)|_N)`, with memory `N ∋ 1`.
- `X ⊆ A^G` is an SFT with window `W ∋ 1` and allowed set `L`: `X = {x : (g⁻¹x)|_W ∈ L for all g}`.
- `F : X → A^G` is strongly post-surjective with constant `Φ ∋ 1` (lifts inside `X`), as in
  `strict-pairs-give-dual-failures-on-bounded-defect-domains`. Domain and target use the SAME alphabet `A`.
- `X ≠ A^G` closed, so some pattern `p ∈ A^P` (`P` finite, `1 ∈ P`) occurs in no point of `X`.

**Observation (constant point).** For a strict pair `(τ, σ)` on `A^G` and `a ∈ A`, `τ(a^G)` is fixed by
every shift (τ is equivariant), hence a constant configuration `b^G`. It lies in `Y ⊆ X_R`. So every domain
produced by `strict-pairs-give-dual-failures-on-bounded-defect-domains` contains a constant configuration.
The Gottschalk route therefore needs the dual statement only for domains containing a constant point.

**Surjectivity.** A strongly post-surjective `F` on a nonempty `X` is onto: the asymptotic class of any
`F(x)` is dense and lies in the closed set `F(X)`.

## 1. The local lift rule

Put `U = W⁻¹W ∪ N⁻¹N` and `K = ΦU` (so `1 ∈ Φ ⊆ K`). Fix a total order on `A^Φ`.

**Lemma 1.1.** There is a partial map `λ : A^K × A → A^Φ` such that for every `x ∈ X` and `c ∈ A`:
`λ(x|_K, c)` is defined, and the point `x'` equal to `x` off `Φ` and to `λ(x|_K, c)` on `Φ` lies in `X`,
with `F(x')(1) = c` and `F(x')(g) = F(x)(g)` for all `g ≠ 1`.

*Proof.* Let `λ(q, c)` be the least `r ∈ A^Φ` passing this check on `q' = (q off Φ, r on Φ) ∈ A^K`:
`(g⁻¹q')|_W ∈ L` for `g ∈ ΦW⁻¹`; `f((g⁻¹q')|_N) = f((g⁻¹q)|_N)` for `g ∈ ΦN⁻¹ \ {1}`; `f(q'|_N) = c`.
All reads lie in `ΦW⁻¹W ∪ ΦN⁻¹N = K`. For `x ∈ X`, let `z = F(x)` with `z(1)` set to `c`. The strong lift
gives `x' ∈ X` with `F(x') = z` and `Δ(x, x') ⊆ Δ(F(x), z)Φ ⊆ Φ`; its restriction to `Φ` passes, so
`λ` is defined. Conversely, any passing `r` gives `x'` whose windows at `g ∉ ΦW⁻¹` and outputs at
`g ∉ ΦN⁻¹` are those of `x`, so `x' ∈ X` and `F(x')` is as stated. ∎

At a site `g` the rule acts through `g⁻¹x`: it rewrites `x` on `gΦ` using `x|_{gK}`.

**Lemma 1.2 (far lifts commute).** Let `S = KK⁻¹`. If `g_1, …, g_m` satisfy `g_i⁻¹g_j ∉ S` for `i ≠ j`,
and `x ∈ X`, then applying the rule at `g_1, …, g_m` (targets `c_i`) gives the same point in any order.
It lies in `X`, and its image is `F(x)` with the value at `g_i` replaced by `c_i`.

*Proof.* The sets `g_iK` are pairwise disjoint and `g_iΦ ⊆ g_iK`. So the rule at `g_j` reads the same
pattern before and after the rewrites at the other `g_i`. Apply Lemma 1.1 `m` times. ∎

## 2. Theorem A (finite quotients; no strong irreducibility used)

**Theorem A.** Let `G` be any group, `X ⊊ A^G` an SFT and `F : X → A^G` strongly post-surjective, with data
as in §0 and §1. Put `B = ΦUΦ⁻¹ ∪ PP⁻¹`. If `H ⊴ G` has finite index and `H ∩ B = {1}`, then `X` has no
`H`-fixed point.

*Proof.* `H`-fixed means `hx = x` for `h ∈ H`, i.e. `x` is constant on each coset `Hg = gH`. Let
`Q = H\G`, `n = |Q|`, and `Fix_H(Z)` the `H`-fixed points of `Z`. So `|Fix_H(A^G)| = |A|^n`, and `F`
maps `Fix_H(X)` into `Fix_H(A^G)` by equivariance. Suppose `x_0 ∈ Fix_H(X)`.

*Step 1 (one coset).* Let `x ∈ Fix_H(X)`, `g_0 ∈ G`, `c ∈ A`, and let `x'` be the rule applied at `g_0`
(target `c`). Put `R_h = hg_0Φ` for `h ∈ H`, and let `x''` equal `hx'` on `R_h` and `x` elsewhere. Since
`hx' = x` off `R_h` (as `hx = x`), `x''` agrees on any set meeting at most one `R_h` with the matching `hx'`.
- If `gW` or `gN` meets `R_h` and `R_{h'}`, then `g_0⁻¹h⁻¹h'g_0 ∈ ΦUΦ⁻¹ ∩ H = {1}` (normality), so `h = h'`.
- So each window `gW` sees a pattern of some `hx' ∈ X`: `x'' ∈ X`. It is `H`-fixed by construction.
- Each output `F(x'')(g)` equals `F(h_g x')(g) = F(x')(h_g⁻¹g)` for a suitable `h_g`. This is `c` if
  `g ∈ Hg_0` and `F(x)(g)` otherwise. (If `gN` meets no `R_h`, then `F(x)(g) = F(x')(g)` for every
  translate, and for `g ∈ Hg_0` this forces `c = F(x)(g_0)`.)
So `F(x'')` is `F(x)` with the coset `Hg_0` set to `c`.

*Step 2 (count).* Apply Step 1 once per coset, starting at `x_0`. Every `z ∈ Fix_H(A^G)` is reached, so
`|Fix_H(X)| ≥ |A|^n`. But `H ∩ PP⁻¹ = {1}` makes `P → Q, π ↦ Hπ` injective. So `Fix_H(X)` lies inside
the words on `Q` that avoid `p` at the coset of `1`, and there are `|A|^n − |A|^{n−|P|} < |A|^n` of those. ∎

**Corollary A.** If `G` is residually finite, then no proper SFT `X ⊊ A^G` with a finite `G`-orbit admits a
strongly post-surjective `F : X → A^G`. (A finite orbit is fixed by some finite-index normal `H_0`. Residual
finiteness gives a finite-index normal `H ⊆ H_0` with `H ∩ B = {1}`, and the point is also `H`-fixed.)

**Consequences.**
- On a residually finite group, a counterexample to `proper-sft-domains-admit-no-dual-failures` must be an
  SFT with no finite orbit. Neither strong irreducibility nor non-pre-injectivity is used.
- Every compression or arrow-shift test domain (`nonamenable-groups-carry-arrow-shift-strict-automata`)
  already has no finite orbits. That is why those tests never died on counting grounds.
- On free groups, the kill-test "an SI SFT with no periodic point" is an open problem. arXiv 2401.16774
  (Contractible subshifts) records that it is not known whether every nonempty strongly irreducible SFT on a
  free group has a periodic point. Piantadosi (2008) gives SFTs on free groups with no periodic point, but
  they are not SI.

## 3. Theorem B (sofic groups, domains with a constant point)

**Theorem B.** Let `G` be sofic, `X ⊊ A^G` an SFT containing a constant configuration `a^G`, and
`F : X → A^G` an automaton. Then `F` is not strongly post-surjective (with lifts in `X`).
Neither strong irreducibility nor non-pre-injectivity is assumed.

**Sofic models (standard, right-action form).** For every finite `D ⊆ G` and `ε > 0` there are a finite set
`V` and permutations `τ_g` of `V` (`g ∈ G`) such that at least `(1−ε)|V|` points `v` are *`D`-good*:
`τ_1(v) = v`, `τ_{gs}(v) = τ_s(τ_g(v))` for `g, s ∈ D`, and `g ↦ τ_g(v)` is injective on `D`.
(Take `τ_g = σ_{g⁻¹}` for a usual sofic approximation `σ`.) Write `ι_v(g) = τ_g(v)`. For `D`-good `v`:
- (G1) `ι_{ι_v(g)}(s) = ι_v(gs)` when `g, s, gs ∈ D`.
- (G2) if `τ_s(w) = ι_v(d)` with `s, d, ds⁻¹ ∈ D`, then `w = ι_v(ds⁻¹)` (by (G1) and injectivity of `τ_s`).
For `u ∈ A^V` and a `D`-good `w`, the pulled-back pattern is `u_w(g) = u(ι_w(g))` for `g ∈ D`.

*Proof of Theorem B.* Data `N, W, L, Φ, U, K, S = KK⁻¹, p, P, λ` as in §0–§1. Suppose `F` is strongly
post-surjective.

*Coloring.* Let `k = 2|S| + 1`. On any model, the graph `w ~ τ_s(w)` (`s ∈ S \ {1}`) has degree `< k`, so a
greedy proper coloring `col : V → {1, …, k}` exists. If `v` is `D`-good and `g, gs ∈ D` with `s ∈ S \ {1}`,
then `ι_v(g)` and `ι_v(gs) = τ_s(ι_v(g))` are distinct and adjacent, so they have different colors.

*Radii.* Put `D_k = K ∪ N ∪ P` and `D_{j−1} = D_j ∪ D_jΦ⁻¹K` for `j = k, …, 1`. Let `D*` be a finite set
containing `D_0 K Φ⁻¹ K`, `S`, and `PP⁻¹P`. Call a point *very good* if it is `D*`-good. All these sets
depend only on the data; only the model `V` varies.

*Construction.* Fix `z ∈ A^V` and put `u_0 = a^V`. In round `j = 1, …, k`, process the very good points `w`
with `col(w) = j` in a fixed order. At each, if `λ(u_w|_K, z(w))` is defined for the current word `u`,
write it on `ι_w(Φ)`. Call the result `u_j`, and put `u(z) = u_k`.

**Claim (mirror).** For every very good `v` and `0 ≤ j ≤ k` there is `x ∈ X` such that
`u_j(ι_v(g)) = x(g)` for all `g ∈ D_j`, and `F(x)(g) = z(ι_v(g))` for every `g ∈ D_j` such that
`ι_v(g)` is very good and `col(ι_v(g)) ≤ j`.

*Proof by induction on `j`.* For `j = 0` take `x = a^G ∈ X`; this is the only use of the constant point.
Assume the claim at `j − 1` with point `x`. Let `g_1, …, g_m` be the `g ∈ G` with `gΦ ∩ D_j ≠ ∅` such that
`w = ι_v(g)` is very good and `col(w) = j`. They lie in `D_jΦ⁻¹ ⊆ D_{j−1}`. Put `w_i = ι_v(g_i)`.
- *Only the `w_i` write into `ι_v(D_j)` in round `j`.* If `w` writes at `τ_φ(w) = ι_v(d)` with `d ∈ D_j`,
  then `w = ι_v(dφ⁻¹)` by (G2), and `g = dφ⁻¹` has `d ∈ gΦ`.
- *They are far apart.* If `g_i⁻¹g_{i'} ∈ S \ {1}`, then `w_i, w_{i'}` have different colors by the coloring
  remark. So `g_i⁻¹g_{i'} ∉ S` for `i ≠ i'`.
- *They read genuine patterns.* By (G1), `ι_{w_i}(K) = ι_v(g_iK)`, and `g_iK ⊆ D_{j−1}`. A color-`j` point
  writing into `ι_v(g_iK)` is `ι_v(g')` with `g'Φ ∩ g_iK ≠ ∅` (by (G2)). Then `g'⁻¹g_i ∈ ΦK⁻¹ ⊆ S`, so
  `g' = g_i`. Hence `w_i` reads `u_{j−1}` there, which is `(g_i⁻¹x)|_K`, with `g_i⁻¹x ∈ X`. By Lemma 1.1,
  `λ` is defined and `w_i` writes, at `ι_v(g_iφ)`, exactly what the rule at `g_i` writes on `x` at `g_iφ`.
Let `x'` be `x` with the rule applied at `g_1, …, g_m`, with targets `z(w_i)`. By Lemma 1.2, `x' ∈ X` and
`F(x')` equals `F(x)` except that the value at `g_i` becomes `z(w_i)`.
- `u_j` agrees with `x'` on `D_j`, since both received the same writes there.
- Outputs at `g ∈ D_j` of color `< j` are unchanged.
- Very good `g ∈ D_j` of color `j` are among the `g_i`, because `1 ∈ Φ`. ∎

*Counting.* Let `V_g` be the set of very good points. For `v ∈ V_g`, the claim at `j = k` gives `x ∈ X`
matching `u(z)` on `D_k ⊇ N ∪ P`, with `F(x)(1) = z(v)`. So:
- `f(u(z)_v|_N) = z(v)`, which means `u(z)` determines `z|_{V_g}`, and so `|{u(z)}| ≥ |A|^{|V_g|}`;
- `u(z)_v|_P = x|_P ≠ p`.

Greedily pick `v_1, …, v_m ∈ V_g` with pairwise disjoint `ι_{v_i}(P)`. By (G2) each pick excludes at most
`|PP⁻¹|` points, so `m ≥ |V_g|/|PP⁻¹|`. Every `u(z)` avoids `p` on each of these disjoint `|P|`-sets, so
`|{u(z)}| ≤ |A|^{|V|}θ^m` with `θ = 1 − |A|^{−|P|} < 1`. With `|V_g| ≥ (1−ε)|V|`, taking logs gives
`((1−ε)/|PP⁻¹|)·|log θ| ≤ ε log|A|`. This is false for small `ε`, depending only on `|A|` and `|P|`. A
model with that `ε` for `D*` exists by soficity. ∎

**Remark.** The constant point is used once: it supplies the microstate `a^V`, all of whose good windows are
genuine. Any point of `X` with such microstates works. The sofic-entropy sketch in the target's Attempts
died exactly for lack of microstates of a general SFT.

## 4. The decomposition this gives

**New sufficient step (OPEN):** `constant-point-sft-domains-admit-no-post-surjective-covers`. For a group
`G`, no proper SFT `X ⊊ A^G` containing a constant configuration admits a strongly post-surjective automaton
`X → A^G`.
- *It suffices.* A strict pair gives, by `strict-pairs-give-dual-failures-on-bounded-defect-domains` (items 1,
  2 and 5), the proper SFT `X_R`, which contains the constant `τ(a^G)` (§0), and the strongly post-surjective
  `σ|_{X_R}`. Items 4 (non-pre-injectivity) and the SI part of item 1 are not needed.
- *Known cases.* Amenable `G`: a proper subshift has entropy `< log|A|`, and a surjection onto `A^G` cannot
  raise entropy (§0 surjectivity), so there is not even a surjective automaton. Sofic `G`: Theorem B.
- *Relation to the old step.* It is not implied by `proper-sft-domains-admit-no-dual-failures`: the old step
  concludes pre-injectivity, not non-existence. It does not imply the old step either: no SI, but a constant
  point is required. It is immune to every compression or arrow-shift kill-test, since those domains have no
  finite orbit and so no constant point.
- *Can fail independently of Gottschalk?* Unknown. The converse would need to turn a strongly post-surjective
  cover of a constant-point domain into an injective non-surjective automaton. A right inverse would need
  symmetry breaking (see `post-surjective-automata-admit-automaton-right-inverses`, necessary condition (f)).
- *Linear sector.* Bus lemma by `swarm-0917-w8-w8-gs-break` (not yet in this tree): a one-sided inverse
  `NM = I ≠ MN` over `F_q[G]` gives the linear SI SFT `(A^G)MN` with a strongly post-surjective,
  non-pre-injective `x ↦ xM²`. That domain contains the constant `0`. So the new step at `G` also forces
  `F_q[G]` to be stably finite, which is consistent, since surjunctive groups have stably finite `F_q[G]`.

## 5. Side result: the branching-orientation SFT on F_2 is not SI

The natural compression test domain on `F_2` (free generators `a, b`, degree 4): each vertex points to one
neighbour, there is no mutual pointing, and each vertex has at least 2 children. Reading the two first children
gives a map onto the doubled alphabet (its strong post-surjectivity is not used or claimed here).

It is not strongly irreducible, by the following cap obstruction. Fix any gap `r`. Let `Q_1` orient the ball
`B_n` inward along its level-`n` leaves, except in the subtree under one level-`(n−m)` vertex `u`. Let `Q_2`
orient every descendant of `u` at level `n + r` toward `u`. Each alone extends: the one open side (through
`u`'s subtree for `Q_1`, through `u`'s parent for `Q_2`) carries an escaping ray, and all other vertices point
toward it. Together they close off the finite subtree `T` formed by `B_n` and `u`'s descendants down to level
`n + r`. Every vertex of `T` then has its out-edge inside `T`: leaves by `Q_1, Q_2`, and inner vertices
because all their neighbours are in `T`. No mutual pointing makes these `|T|` out-edges distinct edges of a
tree with `|T| − 1` edges, a contradiction. The supports are `≥ r` apart for any `r`, so the SFT is not SI.

It fails SI for a structural reason, and it has no finite orbit (Theorem A). So it is not a test object for
either claim.
