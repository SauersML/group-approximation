---
rg: 2
id: rn-lamplighter-is-a-function-field-stein-group
kind: claim
title: V_2(Z/2 wr Z) for the affine lamplighter automaton is the full group of piecewise R-affine homeomorphisms of F_2[[1+t]], R = F_2[t,1/t,1/(1+t)], and acts properly on a contractible complex whose leaves are points of the three Bruhat-Tits trees of R with invariant Busemann-sum height
distinct_from:
  rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp: that proves finite presentation through lift ideals; this identifies the group itself as a piecewise-affine group over a three-place ring and builds the proper action needed for higher finiteness properties.
  rover-nekrashevych-finite-presentation-criteria: that imports F_2 criteria; this is the geometric set-up for F_n, n >= 3, of a Roever-Nekrashevych group whose self-similar group is not finitely presented.
  lamplighter-has-a-faithful-contracting-degree-8-action: that is a different, contracting action on the 8-regular tree.
---

**ESTABLISHED for (1)-(3) (proof in `rn-lamplighter-is-a-function-field-stein-group-proof`; unreviewed). (4) is OPEN.**

## Setting

- `π = 1 + t`, `O = F_2[[π]]` (a Cantor set, the ring of integers of the completion `K_π` of `K = F_2(t)` at `t = 1`).
- `G = F_2[t^{±1}] ⋊ t^Z ≅ Z/2 ≀ Z`, acting on `O` by `x ↦ t^m x + p(t)`. This is the self-similar action of the
  affine lamplighter automaton `B_c(x) = tx + c` for the splitting `λ_x(y) = x + πy`, `x ∈ {0,1}`.
- `R = F_2[t, t^{-1}, π^{-1}]`, the ring of `S`-integers of `K` for `S = {0, ∞, π}`. Its unit group is
  `R^× = t^Z × π^Z`.

## Statement

1. **Realisation.** `V_2(G)` equals the group `PAff(O; R)` of all homeomorphisms `h` of `O` for which there is a
   partition of `O` into finitely many balls on each of which `h(x) = ux + b` with `u ∈ R^×` and `b ∈ R`. So
   `V_2(Z/2 ≀ Z)` is the topological full group of the germ groupoid of `Aff(R) = R ⋊ R^×` acting on `K_π`,
   restricted to `O`. It is the function-field analogue of the Stein–Thompson groups `PAff(Z[1/6], ⟨2,3⟩)`. The
   same proof gives `V_q(F_q ≀ Z) = PAff(F_q[[t-a]]; F_q[t, 1/t, 1/(t-a)])` for the multipliers `t^Z (t-a)^Z`, and
   `F_q^*` adjoined for `AGL_1`.
2. **Invariant height.** Let `T_v` be the Bruhat–Tits tree of `K_v` for `v ∈ S`, and let `β_v` be the Busemann
   function toward the end fixed by `Aff(K_v)`, normalised to increase toward smaller balls. By the product formula,
   `ℋ = β_π + β_0 + β_∞` is invariant under `Aff(R)` acting diagonally on `Y = T_π × T_0 × T_∞`. `G` acts on
   `X = T_0 × T_∞`, preserving `β = β_0 + β_∞`, with the following orbits on the vertices of level `h`:
   - for `h ≤ 0`, one orbit, with stabiliser of order `2^{1-h}`;
   - for `h ≥ 1`, `2^{h-1}` orbits, with trivial stabilisers. At `h = 1` the action is simply transitive, and that
     level set is the Diestel–Leader graph `DL(2,2)`.
3. **Proper contractible complex.** There is a contractible simplicial complex `𝒬` on which `V_2(G)` acts with
   finite stabilisers. Its vertices are Stein–Farley vertices whose leaves are decorated by cells of `X`. The
   `V_2(G)`-orbits of `n`-leaf vertices are the `(G^n ⋊ S_n)`-orbits of cells of `X^n`. A leaf decorated by `p`
   carries the invariant height `ℋ = β(p)`, and splitting a leaf raises the height of both children by `1`. So
   locally a leaf is a point of `Y`:
   - splitting is the move up in `T_π`, taken in both children at once;
   - the tree moves in `X` are the moves in `T_0` and `T_∞`.
4. **Open: `V_2(G)` is of type `F_∞` (or at least `F_3`).** By (3) and Brown's criterion, this reduces to the
   connectivity of descending links in `𝒬` for a Morse function `Σ_leaves φ(ℋ_i)` that is proper in both directions.
   That connectivity is not proved here.

## Why this is the right object

- The standard finiteness criteria need the self-similar group `G` to be of type `F_n`. These are
  Skipper–Witzel–Zaremsky, and Li (arXiv:2110.04505, Thm C, Cor F), where the isotropy group is `G`. Here `G` is not
  even `F_2`, so they fail at the first step. The decoration by `X` removes the infinite stabilisers.
- Bux's `Aff(R)`, with `|S| = 3`, is `F_2` but not `F_3`: the ascending link of a point of `Y` is a join of three
  2-point sets, `S^2`.
- In `V_2(G)` the `T_π`-factor is replaced by the single move "split into both children". So the ascending link of
  a single leaf is `{split} * S^0 * S^0`, a cone.
- This is the mechanism by which `V_2(G)` can have finiteness length larger than both `G` (length `1`) and `Aff(R)`
  (length `2`). The Stein groups `F_{2,3}`, which are `F_∞` over `Aff(Z[1/6])` of length `2`, show the same
  phenomenon.
