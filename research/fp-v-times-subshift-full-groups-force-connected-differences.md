---
rg: 2
id: fp-v-times-subshift-full-groups-force-connected-differences
kind: claim
title: If the full group of V times a free subshift groupoid is finitely presented, difference sets are coarsely connected, so a minimal SFT host has no finite asymptotic pairs and its patterns are determined by boundary layers
distinct_from:
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the open sufficiency premise (P2); this is a necessary condition on the pair (Λ, X) for finite presentation of the same group, which P2 must satisfy.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that forces finite type for full groups without the V factor, through nested commutators of rule 3-cycles; this is a second necessary condition, with the V factor, through a two-dimensional linear representation that switches basis on one half of a split difference set.
  zd-derived-full-group-fp-forces-quantum-rigidity: that is the Z^d quantum-rigidity necessary condition for derived full groups without V; this is the coarse-connectivity condition over every finitely generated acting group, for any finitely presented subgroup of the V-product full group containing the translations and the site-conditioned 3-cycles.
---

**ESTABLISHED (unreviewed).** Route: `fp-v-times-subshift-full-group-connected-differences-proof`.

**Setting.**
- `Λ` is an infinite group with finite symmetric generating set `S`, word length `|.|`,
  and left-invariant metric `d(g, h) = |g^(-1) h|`. `A` is a finite alphabet, and
  `X ⊆ A^Λ` a subshift with `(g.x)(h) = x(g^(-1) h)` on which `Λ` acts freely.
- `G_V` is the groupoid of germs of Thompson's group `V` on `C = {0,1}^N`, and
  `T = G_V × (Λ ⋉ X)` on the unit space `C × X`. `F(T)` is its topological full group.
- `t_s ∈ F(T)` is the translation `(c, x') -> (c, s.x')`, for `s ∈ S`.
- `h ∈ V` is the order-3 element `00w -> 01w -> 1w -> 00w`. For `a ∈ A`, `e_a ∈ F(T)` applies
  `h` to `c` when `x'(1) = a` and is the identity otherwise. It is the 3-cycle of the degree-3
  multisection `[00] × [a] -> [01] × [a] -> [1] × [a]`.
- For `x, y ∈ X`, `Δ(x, y) = {p ∈ Λ : x(p) ≠ y(p)}`. A set is *`m`-connected* if it cannot be
  split into two nonempty parts at distance `> m`.

**Theorem.** Let `Γ ≤ F(T)` be a finitely presented subgroup containing every `t_s` and every
`e_a`.
1. **Coarse connectivity.** There is `m` such that `Δ(x, y)` is `m`-connected for all
   `x, y ∈ X`.
2. **No finite asymptotic pairs.** If `X` is minimal and of finite type, no two distinct points
   of `X` differ on a finite set.
3. **Boundary layers.** Under the hypotheses of part 2, with `X` defined by allowed patterns on
   windows `pB_r`, restriction `L_F(X) -> L_(∂F)(X)` is injective for every finite `F ⊆ Λ`,
   where `∂F = {p ∈ F : pB_(2r) ⊄ F}`. So `|L_F(X)| <= |A|^|∂F|`. Hence:
   - `X` has zero topological entropy if `Λ` is amenable;
   - `log |L_(B_N)(X)| = O(N^(d-1))` if `Λ = Z^d`;
   - `X` is finite if `Λ` is virtually cyclic.

**Corollary (necessary condition for P2).** `F(T) = A(T)` by
`v-times-ample-full-groups-are-generated-by-transpositions`, and `F(T)` contains every `t_s` and
`e_a`. So if `A(T)` is finitely presented, parts 1–3 hold for `X` (take `Γ = F(T)`).
In particular, premise P2 of `boone-higman-via-v-times-aperiodic-sft-full-groups` is false for
any pair `(Λ, X)` in which `X` is a minimal free SFT with a finite asymptotic pair, or with an
`m`-disconnected difference set for every `m`.

**What this does and does not settle.**
- *Kills.* Every V-product full-group host over a subshift with local flexibility: tile flips,
  free bits, positive-entropy row content over amenable `Λ`. Any construction of P1
  (`decidable-groups-embed-in-fp-groups-with-minimal-free-sft`) feeding P2 must produce
  boundary-deterministic shifts.
- *Does not refute P2.* A minimal SFT with a finite asymptotic pair may not exist. Over amenable
  `Λ`, such a pair forces positive entropy by gluing at a syndetic separated set of occurrences
  (route, Section 5, a sketch not used in the theorem). Whether a minimal SFT over an infinite finitely presented group can have
  positive entropy, or a finite asymptotic pair, is not settled here.
- *Parallel.* The algebra analogue for Cantor crossed products, landed on main in parallel as
  fp-crossed-products-force-connected-differences, uses the same basis switch.
- *Injectivity matters.* The proof needs `Γ` to be a subgroup: the contradiction is a commutator
  that is trivial in `Γ` itself. A finitely presented group merely mapping onto such elements is
  not covered.
