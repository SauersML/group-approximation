---
rg: 2
id: fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps-proof
kind: route
title: Push the t_i-edges through the Fox derivative d t_i/db, count what one merge can add to the homology image, and factor d t_{j+1}/db = phi^j(d t_1/db) d t_j/db
target: fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps
requires:
  - fpbs-mal-depth-promotion-equals-overfold-merge-number
  - fpbs-mal-modp-promotion-certificates-are-fox-annihilators
artifacts:
  - experiments/fpbs-transitive-retract-2026-09-17/cert.py
  - experiments/fpbs-transitive-retract-2026-09-17/cert_n5_j1.txt
  - experiments/fpbs-transitive-retract-2026-09-17/cert_n4_j2.txt
  - experiments/fpbs-transitive-retract-2026-09-17/scale.py
  - experiments/fpbs-transitive-retract-2026-09-17/scale_out.txt
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det.py
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det_j1.txt
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det_j2.txt
---

# Proofs

Conventions are those of the target node and of §0 of
`research/fpbs-mal-modp-promotion-certificates-are-fox-annihilators-proof.md`:
- right actions throughout;
- `F[Q]` is a right `F[L]`-module;
- Fox derivatives are left derivatives.

`X = Sch(Q)` has an `s`-edge `q → q.s` for each `s ∈ {a, b}`. `Y_i` has
vertex set `Q`, an `a`-edge `q → q.a` and a `t_i`-edge `q → q.t_i`.

## 1. Theorem 1

**The chain map.** Let `T_i: C_1(Y_i) → C_1(X)` send each `a`-edge to itself
and each `t_i`-edge at `q` to the edge path read by `t_i` from `q`.
- The path from `q` reading `w = x_1 ⋯ x_k` crosses its `r`-th edge at the
  vertex `q.(x_1 ⋯ x_{r−1})` if `x_r` is positive, and at `q.(x_1 ⋯ x_r)` with
  sign `−1` if `x_r` is negative.
- So, in the coordinates `C_1 = F[Q]^2` (the `a`- and `b`-edges, and the `a`-
  and `t_i`-edges), the map is

```text
T_i(α, β) = ( α + β ∂t_i/∂a ,  β ∂t_i/∂b ) = ( α + β ∂t_i/∂a ,  β u_i ).
```

- `T_i` is the identity on vertices and commutes with `∂`. So
  `ker T_i ⊆ Z_1(Y_i) = H_1(Y_i)`.
- From the formula, `ker T_i = { (−β ∂t_i/∂a, β) : β u_i = 0 }`, which has
  dimension `k_{u_i}(Q)`.

**Folding does not change the image.**
- `Γ_i(Q)` is the Stallings fold of `Y_i` with its `t_i`-edges subdivided.
- Folding is `π_1`-surjective on each component and commutes with the maps to
  `X`.
- So `I_i = T_i(H_1(Y_i))`.

Since `dim H_1(Y_i) = 2n − n + c_i`, we get
`dim I_i = n + c_i − k_{u_i}(Q)`. ∎

## 2. Theorem 2

Let `P` be a set of merges whose fold closure `G'` of `Γ_{j+1}(Q)` contains
`ker m`.
- Each merge identifies two vertices over the same point of `Q`, and folding
  preserves the map to `Q`. So every intermediate graph maps to `X`, and so
  does `G'`.
- Apply the merges one at a time, each followed by its folds.
- *Folds.* They keep the number of components and the image in
  `H_1(X; F)`, since they are `π_1`-surjective.
- *A merge of vertices in different components.* The number of components
  drops by 1, and `H_1` is the direct sum, so the image is unchanged.
- *A merge inside one component.* `H_1` grows by one loop class, so the image
  grows in dimension by at most 1. The component count is unchanged.
- Hence `|P| ≥ (c_{j+1} − c(G')) + (dim I(G') − dim I_{j+1})`.

**Bounding `G'` by `Γ_j(Q)`.**
- Since `cl(P) ⊇ ker m` and `m` is onto, `G'` is a quotient of `Γ_j(Q)`.
- The quotient map commutes with the maps to `X`, because both are the
  labelled immersions determined by the real vertices.
- So `c(G') ≤ c_j`, and `I(G') ⊇ I_j`.
- Therefore `|P| ≥ (c_{j+1} − c_j) + dim I_j − dim I_{j+1}`.

Theorem 1 turns the right side into `k_{u_{j+1}} − k_{u_j}`.

**Scope of the count.** Each merge changes at most one of the two counted
quantities, by at most 1. So `B_j` is the whole content of any argument that
charges merges only for components joined and for `H_1(X; F)`-image gained.

**Lawful merges.** These are merges too, so `law_j ≥ deep_j ≥ B_j`. Equality
`B_j = law_j` forces `deep_j = law_j`. ∎

## 3. Theorem 3

**The chain rule.** For an endomorphism `ψ` of `L`, the Fox chain rule is
`∂ψ(w)/∂b = Σ_x ψ(∂w/∂x) · ∂ψ(x)/∂b`. Take `ψ = φ^j` and `w = t_1`. Since
`φ^j(a) = a` has `∂a/∂b = 0`,

```text
u_{j+1} = ∂t_{j+1}/∂b = φ^j(u_1) · ∂φ^j(b)/∂b = φ^j(u_1) · u_j.
```

**The kernels.** Write `x = φ^j(u_1)` and `y = u_j`, acting on the right, so
that `β(xy) = (βx)y`.
- `ker x ⊆ ker(xy)`.
- `dim ker(xy) = dim ker x + dim(im x ∩ ker y) ≤ k_x + k_y`.
- Hence `B_j = k_{xy} − k_y ≤ k_x`.

**Transport.** Finally, `x` acts on `F[Q]` exactly as `u_1` acts on
`F[Q^{(j)}]`, since `q ·_{(j)} g = q.φ^j(g)`. ∎

## 4. Theorem 4

**Freeness.** `φ` is injective, so the stabilizer of `x` in `X^{(j)}` is
`φ^{−j}(Stab_L(x))`, which is trivial almost everywhere.
- So `X^{(j)} = lim Q_m^{(j)}` is an essentially free profinite action.
- Its levels therefore form a sofic approximation of `F_2`: a Farber
  sequence, possibly with intransitive levels.

**Characteristic 0.**
- `k_{u_1}(Q_m^{(j)}) / |Q_m| → dim_{L(F_2)} ker(u_1 on ℓ²F_2)`. This is
  sofic Lück approximation over `Q[F_2]`, due to Elek–Szabó.
- The right side is 0, because `u_1 ≠ 0` and, by Linnell, nonzero elements
  of `C[F_2]` act injectively on `ℓ²F_2`.
- By Theorem 3, `B_j(Q_m)/|Q_m| → 0`.

**Characteristic `p`.** The same chain of inequalities turns a positive
`limsup` into a positive `limsup` of `k_{u_1}` along a sofic approximation.
- By Theorem 3 of the depth-0 node, residual `p`-towers give `k_{u_1} = 0`.
- So such a `limsup` contradicts parts (1)–(2) of Jaikin-Zapirain's
  Conjecture 2.4, exactly as in item 4 of that node.

**`p`-levels.** The augmentation `ε(∂w/∂b)` is the exponent sum of `b` in `w`.
- `φ` acts on `H_1(L) = Z^2` by `a ↦ a`, `b ↦ a − b`, so `t_i` has `b`-exponent
  sum `(−1)^i`.
- So `ε(u_i) = ±1`.
- In the local ring `F_p[P]`, with `P` a `p`-group, such an element is a unit.
- So `k_{u_i}(Q) = 0` for all `i`, and `B_j(Q) = 0`. ∎

## 5. Lemma R

Let `Q` be `L_j`-transitive, with `j ≥ 1`.
- **Ranks.** `[L_j : K'] = n` and `rk L_j = 2`, so by Schreier
  `rk K' = n + 1 = rk S`.
- **Retractions.** Let `r: J → K'` be a retraction, with `K' ≤ J` and
  `rk J ≤ rk K'`.
  - `r` is onto, so `rk J ≥ rk K'`. Hence `J ≅ K'`.
  - `r` is then a surjection between free groups of equal finite rank. By
    Hopficity it is injective.
  - `r(r(s)) = r(s)` then gives `r(s) = s`, so `J = K'`.
- **Free factors.** If `J = K' * C`, then `rk C = rk J − rk K' ≤ 0`, so
  `C = 1`.
- **`J = S`.** `S ≠ K'`, since `S` has finite index in `L` and `L_j` has
  infinite index.
- **Single-seed hits.** For a single-seed hit `J = <K, g>` with `g ∉ L_j`,
  `J ≠ K'`. There `rk J ≤ rk K + 1 − δ ≤ rk K = rk K'`, using `δ ≥ 1` (Lemma 2
  of the w17-pull entry) and `rk K = d + 1 = rk K'` on coincident orbits.

**The `H_1`-split census.** `h1_det.py` computes `det(H_1(K') → H_1(S))` over
`Z`. The value `|det| = 1` occurs on 3192 of the 9504 `L_1`-transitive pairs of
permutations at `n = 5`, and on 102 of the 306 `L_2`-transitive pairs at
`n = 4`. The sanity check `Q = Z/3` gives `−4`, as in w17-pull. ∎
