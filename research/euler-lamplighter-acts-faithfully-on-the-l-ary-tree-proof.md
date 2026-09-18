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
- **β̂ is invertible.** `(lD)^k Λ ⊆ l^k Λ ⊆ F_k`, so `Σ_k (−lD)^k` converges `(l,T)`-adically and inverts `β̂`.
- **Relations.** The relations of `H` hold on the dense `ι(M)`, hence on `Λ`. So `G_l` acts by continuous affine
  maps.
- **Faithfulness.** Suppose `(m, h)` acts trivially. Evaluating at `g = 0` gives `ι(m) = 0`, so `m = 0`. Then
  `ĥ = 1`, and `ĥ` restricts to `h` on `ι(M)`, so `h = 1` because `H ≤ Aut(M)`.

**Part 2.**
- In `Z_l[Z] ⊂ Λ` one has `y d/dy (y^j) = j y^j`. This is multiplication of the point mass at `j` by `j`.
- Two operators on `Λ` are continuous: `D`, which maps `F_n` into `F_(n−1)`, and multiplication of measures by the
  continuous function `x ↦ x`.
- They agree on the dense span of the point masses `δ_j = (1+T)^j`, `j >= 0`, so they are equal.

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
  coordinates.

**Part 5.**
- Let `E` be a term of the chain. The image of `G_l` acting on the level `Λ/E` consists of maps `ḡ ↦ Lḡ + t`.
- Each linear part `L` acts trivially on every step quotient `E_(n,j)/E_(n,j+1) = F_l e_j` above `E`, by part 3. For
  `β̂`, `e_j + (n−j) e_(j+1) ≡ e_j` modulo `E_(n,j+1)`.
- So the linear parts lie in the stability group of a series of the finite `l`-group `Λ/E`, which is an `l`-group (Kaloujnine; textbook).
  The translations form the `l`-group `Λ/E`. The image is therefore an `l`-group. ∎
