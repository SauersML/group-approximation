---
rg: 2
id: torsion-germ-rn-groups-are-not-k-graph-full-groups-proof
kind: route
title: Rubin's theorem makes any isomorphism V_d(H) = F(G_Lambda) spatial; the germ groupoid of F(G_Lambda) is an open subgroupoid of the Hausdorff groupoid G_Lambda, whose isotropy lies in Z^k, so a torsion or non-Hausdorff fixed-point germ of H is an obstruction
target: torsion-germ-rn-groups-are-not-k-graph-full-groups
requires:
  - finite-k-graph-boundary-groupoid-standard-facts
  - li-finite-k-graph-full-groups-are-f-infinity
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/fixed_germs.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-fixed-germs.txt
  - experiments/rn-lamplighter-finiteness-2026-09-17/review_two_graph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-review-two-graph.txt
---

## Conventions

- `Λ` is a finite `k`-graph with (H):
  - it is aperiodic;
  - every vertex receives and emits at least two edges of each colour.
- `Λ^∞` is its infinite path space, and `Z(λ) = {x : x(0, d(λ)) = λ}`.
- `G_Λ = {(x, p - q, y) : σ^p x = σ^q y}`, with basic compact open bisections
  `Z(λ, μ) = {(λz, d(λ) - d(μ), μz)}` for `s(λ) = s(μ)`.
- `F(G)` is the group of full compact open bisections of an ample groupoid `G`. It acts on `G^(0)` by
  `α_U(s(γ)) = r(γ)` for `γ ∈ U`.
- For a group `Γ` acting on a space `Y`, `Germ(Γ ↷ Y)` is the groupoid of germs `[g, y]`, with the germ topology.
- `𝒢_H = Germ(V_d(H) ↷ X^ω)`.

**Imported facts.**

- `finite-k-graph-boundary-groupoid-standard-facts`:
  - (item 3) `G_Λ` is Hausdorff and ample, and `Λ^∞` is a Cantor set;
  - (item 4) aperiodic `Λ` gives a topologically principal `G_Λ`.
- **Rubin's theorem.** Let `Γ_i` be a group of homeomorphisms of a locally compact Hausdorff space `Y_i` (`i = 1, 2`)
  that is *locally moving*: for every nonempty open `U`, some nontrivial element of `Γ_i` is supported in `U`. Then
  every isomorphism `φ : Γ_1 → Γ_2` is induced by a homeomorphism `τ : Y_1 → Y_2`, meaning `φ(g) = τ g τ^{-1}`.
  - Source: M. Rubin, Trans. AMS 312 (1989). This is the locally moving form proved in Belk–Elliott–Matucci,
    arXiv:2203.05930.
  - Not re-read at source in this lane. It is the standard input for all spatial-realisation results on topological
    full groups (Matui, Nekrashevych).

## Lemma A (isotropy of `G_Λ` is torsion-free)

The isotropy group of `G_Λ` at `x` is `{(x, n, x) : σ^p x = σ^q x, n = p - q}`. The map `(x, n, x) ↦ n` is an
injective homomorphism into `Z^k`, because the product in `G_Λ` adds the middle coordinates. Hence every isotropy
group is torsion-free. `G_Λ` is Hausdorff by item 3. ∎

## Lemma B (germs of the full group)

Let `G` be an effective ample Hausdorff groupoid. Then `Θ([α_U, x]) = U x` (the unique arrow of `U` with source `x`)
is a well-defined isomorphism of topological groupoids from `Germ(F(G) ↷ G^(0))` onto an open subgroupoid of `G`.
For `G = G_Λ` with (H), aperiodicity gives topological principality (item 4), and this implies effectiveness for
Hausdorff ample groupoids. So the lemma applies.

*Proof.*

- **Well defined.** Suppose `α_U = α_V` on an open `W ∋ x`. The open bisection `B = (UW)(VW)^{-1}` acts as the
  identity on `α_V(W)`. By effectiveness `B ⊆ G^(0)`, so `UW = VW` and `Ux = Vx`.
- **Injective.** If `Ux = Vx = γ`, then `U ∩ V` is an open bisection containing `γ`. On its source set, an open
  neighbourhood of `x`, we have `α_U = α_V`.
- **Homomorphism.** `(UV)x = U(α_V(x)) · Vx`.
- **Topology.** The basic open set `{[α_U, y] : y ∈ W}` goes to the open bisection `UW`. The image is the union of
  all full bisections, which is open. ∎

## Lemma C (both full groups are locally moving)

- **`V_d(H)`.** Every nonempty open subset of `X^ω` contains a cylinder `wX^ω`. The element of `V_d ≤ V_d(H)` that
  exchanges `w0X^ω` and `w1X^ω` (`w0u ↔ w1u`), and is the identity elsewhere, is nontrivial and supported in `wX^ω`.
- **`F(G_Λ)`.** Take a cylinder `Z(λ) ⊆ U` and put `v = s(λ)`.
  - The paths `μ` of degree `N e_1` with `r(μ) = v` number at least `2^N`, because each vertex receives at least two
    colour-1 edges. For `2^N > |Λ^0|`, two distinct ones, `μ_1 ≠ μ_2`, have the same source.
  - Unique factorisation makes `Z(λμ_1)` and `Z(λμ_2)` disjoint.
  - So `Z(λμ_1, λμ_2) ∪ Z(λμ_2, λμ_1) ∪ (Λ^∞ \ (Z(λμ_1) ∪ Z(λμ_2)))` is a full compact open bisection. It moves
    every point of `Z(λμ_1)`, and it is supported in `Z(λ)`.
- Both spaces are Cantor sets. ∎

## Proof of part 1

Suppose `φ : V_d(H) → F(G_Λ)` is an isomorphism.

1. `F(G_Λ)` acts faithfully on `Λ^∞`, by effectiveness. By Lemma C and Rubin's theorem, `φ` is induced by a
   homeomorphism `τ : X^ω → Λ^∞`.
2. So `τ` induces an isomorphism of topological groupoids `𝒢_H ≅ Germ(F(G_Λ) ↷ Λ^∞)`, `[g, ξ] ↦ [φ(g), τξ]`.
3. By Lemma B, the right-hand side is isomorphic to an open subgroupoid of `G_Λ`. By Lemma A, its isotropy groups
   are torsion-free.
4. Let `h ∈ H` have finite order `n` and a nontrivial germ at a fixed point `ξ`. Then `[h, ξ]` is a nontrivial
   element of the isotropy group of `𝒢_H` at `ξ`, and `[h, ξ]^n = [h^n, ξ] = 1`. This contradicts step 3.

The general form follows from the same proof, with `G_Λ` replaced by any effective ample Hausdorff groupoid `G` with
torsion-free isotropy and locally moving `F(G)`. ∎

*Nontrivial germs from sections.* Let `h` fix `ξ`. For each `n`, `h` maps the cylinder `ξ_1...ξ_n X^ω` to itself
by `ξ_1...ξ_n u ↦ ξ_1...ξ_n h|_{ξ_1...ξ_n}(u)`. So the germ `[h, ξ]` is trivial iff some section
`h|_{ξ_1...ξ_n}` is trivial.

## Proof of part 2

Suppose `φ` is an isomorphism as in part 1. Then `𝒢_H` is isomorphic, as a topological groupoid, to an open
subgroupoid of the Hausdorff groupoid `G_Λ` (steps 1–3 above). So `𝒢_H` is Hausdorff.

Now suppose `g` fixes `ξ`, the germ `[g, ξ]` is nontrivial, and `ξ` is a limit of points `η_j` near which `g` is
the identity. Every neighbourhood `{[g, y] : y ∈ W}` of `[g, ξ]` contains the germs `[g, η_j] = [1, η_j]`, and these
lie in every neighbourhood of `[1, ξ]`. So `𝒢_H` is not Hausdorff, a contradiction. ∎

## Part 3: the three groups

**The criterion as a finite check.** Let `N` be the nucleus, and let `S ⊇ N` be a finite section-closed set. Put an
edge `g → g|_x` whenever `g(x) = x`: this is the fixing graph `F` on `S`.

- Suppose `g ∈ H` fixes `ξ`. Then the sections `g|_{ξ_1...ξ_n}` lie in `N` for all large `n`, and they form an
  infinite path in `F`.
- So a nontrivial fixed-point germ exists iff `F|_N` has a cycle avoiding `1`.
  - For "if", take `g` on the cycle and let `ξ` be the periodic point spelled by the cycle.
  - The germ `[g, ξ]` has finite order iff `g` does, since `[g, ξ]^m = [g^m, ξ]`. So a finite-order element on
    such a cycle witnesses part 1. That is sufficient, and it is what we use.

`fixed_germs.py` computes this, with `S` the section-closure of all words of length at most `L`. Its method:

- Triviality of a word is decided as a greatest fixed point: a word is trivial iff every state reachable from it has
  the trivial permutation.
- The nucleus is recomputed as the set of elements reachable from cycles of the section graph of `S`. It agrees with
  the known nuclei:
  - Grigorchuk `{1,a,b,c,d}`;
  - basilica `{1, a^{±1}, b^{±1}, ab^{-1}, ba^{-1}}`;
  - Hanoi `{1,a,b,c}`;
  - adding machine `{1, a^{±1}}`.
- Output: `results-fixed-germs.txt`, which ends `EXPECTED PATTERN ... OK`.

Each verdict below is also checked by hand.

- **Grigorchuk.** `b = (a,c)`, `c = (a,d)`, `d = (1,b)` all fix both letters. Along `1^ω` the sections cycle
  `b → c → d → b`, all nontrivial, and `b² = c² = d² = 1`.
  - Part 1 applies with `h = b` and `ξ = 1^ω`.
  - Part 2 also applies. Since `d|_{1^{3m}} = d` and `d|_0 = 1`, `d` is the identity on `1^{3m}0X^ω → 1^ω`, while
    `[d, 1^ω]` is nontrivial.
- **Hanoi `H^(3)`.** `a = (01)(1,1,a)` fixes only the letter `2`, and `a|_2 = a`. So `a` fixes `2^ω` with all
  sections equal to `a`, and `a² = 1`. Part 1 applies. Likewise `b` at `1^ω` and `c` at `0^ω`.
  - Part 2 does not apply. The only fixing-graph cycles are the loops `a → a`, `b → b` and `c → c`, and none
    reaches `1`.
- **Basilica.** In the nucleus, `a^{±1}`, `ab^{-1}` and `ba^{-1}` act on the first letter by the swap, so they have
  no fixing edges. `b^{±1}` fix both letters, with sections `1` and `a^{±1}`.
  - So `F|_N` has no cycle avoiding `1`, and every fixed-point germ of every element of `H` is trivial.
  - `𝒢_H` is then Hausdorff. Suppose the germs `[g_1, ξ] ≠ [g_2, ξ]` are inseparable. Then `g = g_2^{-1}g_1`
    fixes `ξ`, and `g` is the identity near points `η_j → ξ`.
    - Near `ξ`, `g = λ_w h λ_v^{-1}`. Being the identity on a cylinder forces `|w| = |v|`, because a shift is not
      injective. So `w = v`.
    - Then `[g, ξ] = λ_v [h, η] λ_v^{-1}` with `h(η) = η`. This germ is trivial, a contradiction.
  - Its isotropy embeds in `Z` by the level cocycle `c([λ_w h λ_v^{-1}, ξ]) = |w| - |v|`.
    - **Well defined.** A representative with `|w| ≠ |v|` maps each small cylinder around `ξ` onto a cylinder of a
      different length, so it is not the identity near `ξ`.
    - **Injective on isotropy.** If `|w| = |v|` and the germ fixes `ξ ∈ vX^ω ∩ wX^ω`, then `v = w`. The germ is then
      `λ_v [h, η] λ_v^{-1}` with `h(η) = η`, which is trivial.
  - So neither obstruction applies to the basilica.

**Finiteness.** The three groups are generated by bounded automata. `V_d` of a bounded automata group has type
`F_∞` by Belk–Hyde–Matucci arXiv:2407.03149, as read at source and recorded on main in
`contracting-rover-nekrashevych-groups-are-f-infinity`.

- For Röver's group this is earlier: Belk–Matucci, Publ. Mat. 60 (2016).
- For the basilica it also follows from `hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`. The critical
  point `0` of `z² - 1` has period 2, so the map is hyperbolic and post-critically finite.
- These citations are not used in parts 1–2.

## Part 4 (remark only): the quasi-flat and why the basilica is left open

For `k ≥ 2`, let `x ∈ Λ^∞` be aperiodic, and let `C` be a compact generating set of `G_Λ`: a finite union of
bisections `Z(e)`, `Z(e)^{-1}`, over the edges `e`.

- The map `p ↦ (σ^p x, p, x)`, for `p ∈ N^k`, is Lipschitz into the Cayley graph of `G_Λ` at `x`.
- The cocycle `d` is bounded on `C`, so `|p - p'| ≤ const · dist`.
- Hence the map is a quasi-isometric embedding of `N^k`.

Nekrashevych proves that groupoids of germs of contracting groups are hyperbolic (*Hyperbolic groupoids and
duality*, Mem. AMS 2015). If so, no `𝒢_H` with `H` contracting is `G_Λ` for `k ≥ 2`. Transferring this to
`Germ(F(G_Λ)) ⊆ G_Λ` needs the quasi-flat to lie in the germ subgroupoid. That holds when the subgroupoid is all of
`G_Λ`, which we have not proved in general. For `k = 1`, one would compare the duals: the basilica limit space is
connected, while the dual of a graph groupoid is totally disconnected.

Neither step is checked at source, so the basilica verdict stays **open**. Its `V_2` is `F_∞` anyway (part 3).

## Review of `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof` (w10-101)

**Verdict: no gap found.** Every step was read and re-derived by hand. The computational input was recomputed by
new code that does not share any of `two_graph.py`'s logic. That code is `review_two_graph.py`, and its output,
`results-review-two-graph.txt`, ends `ALL OK`.

1. **The rule `e_i f_j = f_i e_{i+j}`.** Recomputed symbolically in `F_2(t)`. The four `ef`-products are distinct,
   and they coincide with the four `fe`-products.
2. **Lemma 1 (normal form of `P_(m,n)`).** Membership in `P` is decided from the geometric definition through
   valuations, not from the claimed normal form:
   - `a = ux + b` lies in `P` iff `v_π(u), v_π(b) ≥ 0`, `v_0(u) ≤ 0 ≤ v_0(b) - v_0(u)`, and
     `v_∞(u) ≤ 0`, `v_∞(b) ≥ v_∞(u) + 1`.
   - Brute force over `b = A/(t^s π^j)` with `π`-poles allowed, for `m, n ≤ 3`, gives `|P_(m,n)| = 2^{m+n}`.
   - All translation parts are Laurent polynomials, `a ↦ a(O)` is onto the balls of radius `2^{-(m+n)}`, and
     `P_(0,0) = {id}`.
   - By hand, `P_(0,0) = {id}` is w9's `R ∩ O = F_2[t^{±1}]` plus the two tree conditions. The `π`-pole case is
     excluded because `a(O) ⊆ O` forces `v_π(b) ≥ 0`.
3. **Lemma 2 (unique factorisation).** Exhaustive over all `a` with `d(a) ≤ (3,3)` and all `p ≤ d(a)`: 2401 cases.
   In each case there is exactly one `a = a' a''` with `d(a') = p` and `a', a'' ∈ P`.
   - The hand proof is correct. The ball `a(O)` determines `a`. For each intermediate degree, the ball
     `a(O) ⊆ a'(O)` determines the ancestor ball `a'(O)` uniquely, and then `a'' = a'^{-1} a ∈ P` by the ancestor
     condition in both trees.
4. **The germ step** (every `g ∈ Aff(R)` agrees near each point of `O` with some `λ μ^{-1}`, `λ, μ ∈ P`). Checked
   exhaustively over `P_(M,M)` for `M ≤ 7` and 16 random `g` with `π`-poles in the translation part.
   - The set of `μ` with `gμ ∈ P` is all admissible `μ` exactly when `M ≥ M_ρ(g)`, where `M_ρ` is the threshold
     predicted from the three valuations of `g`.
   - Observed thresholds are between 0 and 8. The `(2, 0)` rows are `g` whose `π`-adic ball misses `O` at that
     level, so no `μ` is admissible, as predicted.
   - The hand argument, "choose `μ` deep enough that `gμ` has an ancestor of `ρ_*`", is correct as written.
5. **Automaton.** The lamplighter automaton `a = σ(a, b)`, `b = (a, b)` equals `x ↦ tx + c` on `O/π^{10}O`, up to
   the digit relabelling `x ↦ x + 1/t`, which lies in `Aff(R)`. So the identification of `V_2(Z/2 ≀ Z)` with the
   full group is unaffected.
6. **Homology, simplicity and isotropy (w10 §§4–7).** Checked by hand. The Koszul complex of the 2-graph with
   `n_1 = n_2 = 2` has `1 - 2 = -1` invertible, so `H_*(G_Λ) = 0`. Li's theorems then give the stated acyclicity
   and simplicity.
   - The §6 generalisation `e_i f_j = f_{i/a} e_{j - i/a}` is re-derived. It gives `H_0 = H_1 = Z/(q-1)`.

**Two wording fixes, recommended but not needed for correctness.**

- In Step 2, write the transfer argument as `inc_* ∘ tr = 2 = 0` with `inc_*` injective. The proof as written
  compresses this.
- In the definition of `Φ`, state that `λμ^{-1} ∈ Aff(R)` does not depend on the representative pair.
