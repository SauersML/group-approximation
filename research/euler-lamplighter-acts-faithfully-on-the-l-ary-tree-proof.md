---
rg: 2
id: euler-lamplighter-acts-faithfully-on-the-l-ary-tree-proof
kind: route
title: Complete the Euler lamplighter along (l, T) and refine the adic filtration by the unipotent graded action
target: euler-lamplighter-acts-faithfully-on-the-l-ary-tree
requires:
  - z-localized-embeds-in-fg-rf-soluble-group
---

**Part 1.**
- `T ↦ y − 1` is an isomorphism `Z_l[T] ≅ Z_l[y]`. So a Laurent polynomial `p` with `p(1+T) = 0` in `Λ` gives
  `y^N p(y) = 0` in `Z_l[y]`, hence `p = 0`. `ι` is injective, and `Z[T] ⊂ ι(M)` is dense.
- The operators match on `ι(M)`: `ι(y^(-1) m) = (1+T)^(-1) ι(m)`, and `y d/dy` corresponds to `(1+T) d/dT`.
- **D preserves the filtration after multiplying by l.** `D(l^a T^b) = b l^a T^(b−1) + b l^a T^b`. The first term
  has adic degree `>= a + b − 1`. So `lD` maps `F_n` into `F_n`, and `β̂ = 1 + lD` is continuous.
- **β̂ is invertible.** `Σ_k (−lD)^k` converges coefficientwise, since `l^k -> 0` and `D^k` lowers `T`-degree by at
  most `k`.
- **Relations and faithfulness.** The relations of `H` hold on the dense `ι(M)`, hence on `Λ`. So `G_l` acts by
  continuous affine maps. Faithfulness comes from injectivity of `ι` on translations and faithfulness of `H` on
  `M`.

**Part 2.** In `Z_l[Z] ⊂ Λ` one has `y d/dy (y^j) = j y^j`, which is multiplication of the point mass at `j` by
`j`. The coordinate function is the continuous extension to `Z_l`.

**Part 3.**
- `gr_n = F_n / F_(n+1)` is `F_l^(n+1)` with basis `e_a = l^a T^(n−a)`.
- Modulo `F_(n+1)`, `lD(e_a) ≡ (n−a) e_(a+1)`, so `β̂` acts on `gr_n` by `e_a ↦ e_a + (n−a) e_(a+1)`. That is
  unipotent and preserves each `span{e_(a') : a' >= j}`.
- Multiplication by `(1+T)^(-1) = 1 − T + …` is the identity on `gr_n`.
- Translations have trivial linear part.
- So every linear part preserves `F_(n+1)` and each `E_(n,j)`. Each step `E_(n,j) ⊃ E_(n,j+1)` has quotient
  `F_l e_j`.

**Part 4.**
- An affine map whose linear part preserves a subgroup `E` permutes the cosets of `E`. This gives an action on the
  tree of cosets of the chain `E_(0,0) ⊃ E_(0,1) ⊃ E_(1,1) ⊃ …`, which is `l`-regular by part 3.
- The chain intersects in `0` and `Λ` is complete, so the ends of the tree are the points of `Λ`. The action on
  ends is the affine action of part 1, which is faithful.
- `F_(n+1)` is the set of series whose digits vanish at every `(a, b)` with `a + b <= n`, which gives the stated
  coordinates. ∎
