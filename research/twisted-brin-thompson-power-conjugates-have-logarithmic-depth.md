---
rg: 2
id: twisted-brin-thompson-power-conjugates-have-logarithmic-depth
kind: claim
title: In every twisted Brin--Thompson group SV_G, for any actor G and any set S, cylinder depth shift is finite and subadditive, so an element conjugate to a proper power has depth growth O(log n), while renormalization conjugators and infinite-order Thompson elements have linear depth growth; hence in no twisted Brin--Thompson host can the chain generators b, c, a Higman generator, or the Baumslag--Gersten a or b be conjugate to such a stripping element
distinct_from:
  depth-distortion-obstructs-power-conjugates-in-leavitt-hosts: that proves the depth-rate law in nV and Leavitt tensor units, with finitely many coordinates, where depth-bounded elements are locally periodic over a finite field; this proves it in SV_G for every actor and every (possibly infinite) coordinate set S, which covers every B_A certificate, and shows that the local-periodicity item fails there because global twists have depth zero and infinite order.
  brin-thompson-proper-power-conjugates-have-zero-entropy: that uses topological entropy, which is finite in nV but infinite for global twists of SV_G, so it says nothing in B_A hosts; depth shift stays finite in every SV_G, so this invariant survives exactly where entropy dies.
  twisted-brin-thompson-global-twists-are-conjugacy-closed: that controls conjugacies between global twists through the germinal twist at a constant point; this controls the prefix (non-twist) part of arbitrary elements, and the two together split every chain design in SV_G into a twist part that reduces to G and a depth part that must grow logarithmically.
  higman-chain-group-pbh-iff-chain-configuration: that reduces G_1 in B_A to a chain configuration in some B_A group; this proves a necessary condition on every such configuration inside its twisted Brin--Thompson host.
artifacts:
  - research/twisted-brin-thompson-logarithmic-depth-proof.md
---

**ESTABLISHED** (proof: `twisted-brin-thompson-logarithmic-depth-proof`; lane proof, elementary, not reviewed; no
priority claimed). This is an obstruction to a class of host designs. It does not settle `boone-higman-conjecture`,
`higman-chain-group-lies-in-b-a`, H4 or BG.

## Setting

- `G` acts faithfully on a set `S` of any cardinality. `C = {0,1}^N`, and `C^S` has the product topology.
- `SV_G` is the group of homeomorphisms of `C^S` that locally agree with elements of `V ≀ G = (⊕_S V) ⋊ G`. Here
  `G` acts by the twists `τ_g(κ)(s) = κ(g^-1 s)` (Belk--Zaremsky, arXiv:2001.04579; the definition as recorded in
  `fg-subgroups-of-gl-n-q-in-twisted-bt-proof`, item 2).
- `A(S)` is the set of locally constant functions `φ : C^S -> Z`.
  - `depth(φ)` is the least `k` such that `φ(x) = φ(x')` whenever `x_s` and `x'_s` agree in their first `k` bits
    for every `s ∈ S`.
  - It is finite, because `φ` has finitely many clopen fibres, each a finite union of basic sets.
- For `f ∈ SV_G` put `f_* φ = φ ∘ f^-1`. The depth shift is
  `s(f) = sup_φ (depth(f_* φ) - depth(φ))`.
- `E_f(n) = max(s(f^n), s(f^-n))`, and `ε(f) = lim E_f(n)/n`.

## Statement

1. **Finite, subadditive, nonnegative.** For every `f ∈ SV_G`, `0 <= s(f) < ∞`, and `s(fh) <= s(f) + s(h)`. Every
   twist has `s(τ_g) = 0`.
2. **Invariance.** `ε(f)` exists, `ε(h f h^-1) = ε(f)` for all `h ∈ SV_G`, and `ε(f^k) = |k| ε(f)`.
3. **Logarithmic law.** Suppose `h f h^-1 = f^k` with `|k| >= 2`. Then `E_f(n) <= C log n` for all `n >= 2`, with
   `C` depending on `s(f^±1)`, `s(h^±1)` and `k`. In particular `ε(f) = 0`.
4. **Baumslag--Gersten tower bound.** If `BG = ⟨a, t | (t a t^-1) a (t a t^-1)^-1 = a^2⟩` maps into `SV_G`, then
   `E_A(N_i) <= C 2^i` for `A` the image of `a`, `N_0 = 1` and `N_{i+1} = 2^{N_i}`. This is item 3 of
   `depth-distortion-obstructs-power-conjugates-in-leavitt-hosts`, now in every `SV_G`.
5. **Linear witnesses.** Each of the following has `ε >= c > 0`, so by 2 it is not conjugate in `SV_G` to anything
   with logarithmic depth growth.
   - (a) **Thompson elements.** The image of an infinite-order `v ∈ V` acting in a single coordinate `r ∈ S`
     has `ε >= |γ|/p`, where `v^p(αw) = αγw` is an attracting cycle.
   - (b) **Renormalization conjugators.** Any conjugator
     `g(T^i a, y) = (φ(a), c_i y)` of `renormalizable-thompson-elements-give-baumslag-solitar`, placed on
     `k + 1` coordinates of `S`, has `ε(g) >= 1`. This includes the baker map, the conjugator of the recorded
     `BS(1,2)` embeddings in `2V` and in `2V_tau`.
   - (c) **Commuting repairs.** If `x` commutes with `f` and `ε(x) = 0`, then `ε(f x) >= ε(f)`. So multiplying a
     stripping element by a twist on other coordinates (the infinite-entropy repair) keeps `ε >= c`.
6. **Consequences for host designs in every SV_G.** These are the hosts of repair (ii) of
   `higman-chain-group-lies-in-b-a`, and of every type (A) certificate. When the action is of type (A), `SV_G`
   is finitely presented and simple by `twisted-brin-thompson-finite-presentation-criterion`.
   - **Chains.** In a chain configuration `(a, b, c)` in `SV_G` (`a^-1 b a = b^2`, `b^-1 c b = c^2`), both `b`
     and `c` satisfy 3, so neither is conjugate in `SV_G` to any element of 5.
   - **Higman.** For any homomorphism `H4 -> SV_G`, all four generator images satisfy 3.
   - **Baumslag--Gersten.** For any homomorphism `BG -> SV_G`, the images of `a` and `b = t a t^-1` satisfy 3,
     and the image of `a` satisfies 4.
   - **Scope.** If `H <= G` sits in `SV_G` by twists (the tautological `B_A` placement), everything in `H` has
     depth `0`, so 6 says nothing about it. That placement is governed instead by
     `twisted-brin-thompson-global-twists-are-conjugacy-closed`, which returns every such conjugacy to `G`.
7. **Where the finite-coordinate theory fails.** If `g ∈ G` has infinite order, then `τ_g` has infinite order and
   `E_{τ_g} ≡ 0`. So item 4 of the Leavitt node (bounded depth over a finite field forces local periodicity)
   is false in `SV_G`. Depth alone cannot exclude `BG` or `H4` from `SV_G`. What survives is the split in the
   Lesson below.

## What this kills

**The renormalization and baker-twist designs for repair (ii) of `higman-chain-group-lies-in-b-a`,** in every
twisted Brin--Thompson host at once. Every such design takes the chain's middle element `b` to be a renormalization
conjugator (5b), possibly times a twist on fresh coordinates (5c). It dies at one step: `b ~ b^2` via `a` forces
`E_b(n) = O(log n)` by 3, but `E_b(n) >= n`.

The same step kills these designs for the Higman generators and for the Baumslag--Gersten `a` and `b`. It also
removes the reason the graph looked to infinite-entropy elements of twisted Brin--Thompson groups:
- entropy is useless in `SV_G`;
- depth is not useless there;
- the infinite-entropy repair does not change depth (5c).

## Lesson for general BH

Every element `f ∈ SV_G` has two parts. The **twist part** is the germinal cocycle, which at constant points is
rigid by `twisted-brin-thompson-global-twists-are-conjugacy-closed`. The **prefix part** is measured by depth,
which is finite and subadditive by 1.

A proper-power conjugacy in any `B_A` host must be carried by one of two things:
- twists, where it is already a proper-power conjugacy of the actor `G`, and so circular for chains;
- a prefix part of **logarithmic** depth growth.

A new chain design in a twisted Brin--Thompson group therefore needs a conjugator of zero depth rate that is not a
twist. The graph records no element of this kind that conjugates an infinite-order element to its square outside
the actor. Finding one, or proving there is none, is the sharpened form of repair (ii).
