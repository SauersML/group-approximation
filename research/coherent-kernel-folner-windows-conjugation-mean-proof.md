---
rg: 2
id: coherent-kernel-folner-windows-conjugation-mean-proof
kind: route
title: Average the uniform measures on coherent windows, and read the fibre-square coset space as the affine kernel
target: coherent-kernel-folner-windows-force-conjugation-invariant-mean
requires: []
---

Notation as in the target. A mean on `N` is invariant under left translation and conjugation exactly when it
is invariant under right translation and conjugation, since `kA = (kAk^-1)k`.

**Item 1.** Put `μ_i(n) = ∫ |T^(i)_y|^-1 1_(T^(i)_y)(n) dν_i(y)`. Summing over `n` gives `1`, so `μ_i` is a
probability measure on `N`.
- *Conjugation.* For `w ∈ W`, `μ_i(w^-1 n w) = ∫ |T_y|^-1 1_(w T_y w^-1)(n) dν_i = ∫ |T_(wy)|^-1 1_(T_(wy))(n) dν_i`,
  and this is `μ_i(n)` because `ν_i` is `W`-invariant.
- *Translation.* For `k ∈ N`, `(k_* μ_i)(n) = ∫ |T_y|^-1 1_(k T_y)(n) dν_i`. So
  `||k_* μ_i - μ_i||_1 <= ∫ |k T_y Δ T_y| / |T_y| dν_i <= δ + 2 ν_i(bad set)`, where the bad set is where the
  window is not `(K, δ)`-Følner. By hypothesis this tends to `0`.

A weak-star cluster point of the `μ_i` in `(ℓ^∞ N)^*` is a mean invariant under conjugation (exactly, at
every stage) and under left translation (in the limit). That is (CIM).

**Item 2.** The map `Δ(a, b) ↦ b^-1 a` identifies `Δ \ (W ×_Q W)` with `N`. It is well defined because
`(wb)^-1(wa) = b^-1 a`, and it is bijective with inverse `n ↦ Δ(n, 1)`. The right action of `(c, d)` sends
`b^-1 a` to `d^-1 (b^-1 a) c = (d^-1 (b^-1 a) d)(d^-1 c)`, with `d^-1 c ∈ N`.
- `(m, 1)` with `m ∈ N` acts by right translation by `m`.
- `(w, w)` acts by conjugation `n ↦ w^-1 n w`.
- These elements generate the fibre square, since `(a, b) = (a b^-1, 1)(b, b)`.

So an invariant mean on the coset space is a mean on `N` invariant under right translation and conjugation,
which is (CIM).

**Item 3.** Write each element of `N ⋊ Q` uniquely as `p n` with `p ∈ Q`, `n ∈ N`, and identify `Q p n` with
`n`. Right multiplication by `m ∈ N` is right translation `n ↦ nm`. Right multiplication by `r ∈ Q` gives
`Q p n r = Q (pr)(r^-1 n r)`, which is conjugation `n ↦ r^-1 n r`. Conjugation by `N` is a composite of left and
right translations. So a `W`-invariant mean on `Q \ W` is a mean on `N` invariant under translations and
under conjugation by `W`, which is (CIM).

**Item 4.**
- *Finite `N`.* The uniform measure is invariant under translations and automorphisms. The constant window
  `T_y = N` is coherent and exactly Følner.
- *Central amenable `N`.* Conjugation is trivial, so any left-invariant mean works, and a fixed Følner set is
  a coherent window.
- *Amenable `W`.* `W ×_Q W <= W × W` is amenable, so its action on `Δ \ (W ×_Q W)` has an invariant mean.
  Item 2 gives (CIM).
- *Kun–Thom wreath.* `W = (Z/2)^(G/Γ) ⋊ G` splits with complement `G`. The instance `M = 0` of
  `kun-thom-wreath-actor-subgroups-are-not-co-amenable` says `G` is not co-amenable in `W`, so item 3 says
  (CIM) fails.

**Remark.** Under (CIM) with `W` infinite, item 2 and Corollary B of
`rokhlin-maximality-ascends-co-amenable-subgroups` show that `W` is Rokhlin-maximal at `q` iff `W ×_Q W` is.
This gives no new maximal group: `W ×_Q W = N_1 ⋊ Δ` with `N_1 = N × 1` has quotient `W`, so it returns the
original question.
