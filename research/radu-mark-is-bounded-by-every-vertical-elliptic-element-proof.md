---
rg: 2
id: radu-mark-is-bounded-by-every-vertical-elliptic-element-proof
kind: route
title: Push the elliptic word to a boundary vertex of its fixed ball, read off an approximate copy of xz inside <a,b,c>, let it approximately commute with y(xz)^2y through the sign character, and close with Radu's Lemma 3.5 bookkeeping
target: radu-mark-is-bounded-by-every-vertical-elliptic-element
requires:
  - radu-mark-is-controlled-by-one-commutator
  - radu-mark-survives-only-if-horizontal-group-embeds
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-horizontal-projection-kills-delta-squared
  - radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups
artifacts:
  - experiments/titz-witzel-kernel-sofic-2026-09-16/elliptic_support_check.py
  - experiments/titz-witzel-kernel-sofic-2026-09-16/elliptic_support_check_output.txt
---

# Proof

Notation of the target. `u = yδ^2y`, `κ1 = d(uδ, δu)`, `κ2 = d(uδb, δbu)`.

## 0. Conventions

**Bi-invariance.** A bi-invariant metric is invariant under left and right translation,
conjugation and inversion, and `d(g1g2, h1h2) <= d(g1,h1) + d(g2,h2)`. All six generators square
to 1 in `G`, so the value of a reversed word is the inverse of the value of the word.

**Square moves.** The relators give `hs = s'h'` in `Γ_R` for `h ∈ {a,b,c}`, `s ∈ {x,y,z}`:

```text
(a,x)->(x,a) e1   (a,y)->(y,a) e2   (a,z)->(z,b) e3
(b,x)->(x,b) e4   (b,y)->(y,c) e5   (b,z)->(z,a) e3
(c,x)->(z,c) e6   (c,y)->(y,b) e5   (c,z)->(x,c) e6
```

In `G`, `d(hs, s'h')` is the defect listed, because `(hs)^(−1)s'h'` is a cyclic rotation of the
relator or of its inverse (as in step 1 of `radu-mark-is-controlled-by-one-commutator-proof`).
By bi-invariance, replacing a subword `hs` of a longer word by `s'h'` changes its value in `G` by
at most `ε`.

**Letterwise push.** Take a word `h = h_1…h_L` in `a,b,c` and a word `v = s_1…s_m` in `x,y,z`.
* Move `h_L` through `s_1`, then `h_(L−1)` through the resulting letter, and so on, turning
  `h s_1` into `s_1' h^(1)` with `|h^(1)| = L`.
* Repeat with `s_2`, and so on through `s_m`.

This takes `Lm` moves, gives words `v' = s_1'…s_m'` and `h' = h^(m)`, and

```text
hv = v'h' in Γ_R,      d(h_G v_G, v'_G h'_G) <= Lm ε in G.                  (P)
```

Pushing through a single letter `s`, the letters `a,b` never change the `V`-letter, while `c`
swaps `x ↔ z` and fixes `y`. So the output letter is `s` if `s = y` or `#c(h)` is even, and it
is the other letter of `{x,z}` otherwise.

**The vertical tree.** By `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, `Γ_R` acts simply
transitively on the vertices of `T_h × T_v`. Hence:
* `Γ_R = VC = CV`, `V ∩ C = 1`, and `V ≅ C_2 * C_2 * C_2`;
* the vertices of `T_v = Γ_R/C` are `vo`, for `v` running over the reduced words in `x,y,z`;
* the neighbours of `vo` are `vso`, and the vertex stabilizers are the conjugates of `C`.

This is the setting of `radu-mark-survives-only-if-horizontal-group-embeds`. Let `χ : C → {±1}`,
`χ(h) = (−1)^(#c(h))`. It is well defined because free reduction removes `c` in pairs. By the
single-letter rule, `h ∈ C` fixes `xo, yo, zo` if `χ(h) = 1`. If `χ(h) = −1`, it swaps `xo ↔ zo`
and fixes `yo`.

**Sections.** Let `g ∈ C` be given by a word of length `L`, and let `v` be reduced with
`g·vo = vo`. Push `g` through `v` to get `(v', k)`. Then `v'C = gvC = vC`, so `v' = v` in `V`.
Since `v'` has the reduced length `|v|` of `v`, and a non-reduced word represents a shorter
element, `v'` is literally the word `v`. So `k` represents the **section**
`σ_v(g) := v^(−1)gv ∈ C`, a word of length `L`. Since `g·vso = v σ_v(g) so`:
* `g` fixes all neighbours of `vo` iff `χ(σ_v(g)) = 1`;
* if `χ(σ_v(g)) = −1`, `g` swaps `vxo ↔ vzo` and fixes `vyo`;
* when `χ(σ_v(g)) = 1`, `σ_(vs)(g) = sσ_v(g)s` depends only on `σ_v(g)` and `s`.

## 1. The boundary vertex

Let `γ ≠ 1` be reduced of length `L`. By item 2 of `radu-mark-survives-only-if-horizontal-group-embeds`,
`γ` acts nontrivially on `T_v`, so `r = r(γ)` is finite.

**Lemma R.** `r = min{|v| : γ fixes vo and χ(σ_v(γ)) = −1}`. A minimizing `v` is empty or ends
in `y`.

*Proof.* Some vertex at distance `r+1` from `o` is moved. Its neighbour `vo` towards `o`, with
`|v| = r`, is fixed, so `χ(σ_v(γ)) = −1`. Suppose some `v''` with `|v''| < r` had
`χ(σ_(v'')(γ)) = −1`. The vertex `v''o` is fixed, since it lies in `B(o,r)`. So `γ` would move
`v''xo` and `v''zo`, both at distance at most `r` from `o`, which is impossible. So the minimum
is `r`.

For a minimizer `v = s_1…s_r` with `r >= 1`, the parent `s_1…s_(r−1)o = vs_r o` lies in
`B(o, r−1)` and is fixed. Of the neighbours of `vo`, only `vyo` is fixed, so `s_r = y`. ∎

## 2. Proof of (EB1)

**Step 1.** Take `v` as in Lemma R and push the word `γ` through the word `vz`.
* The first `rL` moves give `(v, k_1)`, where `k_1` represents `σ_v(γ)`, so `#c(k_1)` is odd.
* By the single-letter rule, the last `L` moves turn `k_1 z` into `xk` with `|k| = L`.

By `(P)`, `d(γ_G v_G z, v_G x k_G) <= L(r+1)ε`. Right-multiplying by `z v_G^(−1)`, and using
conjugation invariance and `x^2 = z^2 = 1`:

```text
d(γ_G, v_G x k_G z v_G^(−1)) <= L(r+1)ε,
d(v_G x k_G z v_G^(−1), 1) = d(x k_G z, 1) = d(k_G, xz) = d(k_G, δ),
d(k_G, δ) <= d(γ_G, 1) + L(r+1)ε.                                        (S1)
```

**Step 2.** If `#b(k)` is even, put `k' = k` and `δ' = δ`. Otherwise put `k' = kb` and `δ' = δb`.
Then `#b(k')` is even, `|k'| <= L+1`, and `d(k'_G, δ') = d(k_G, δ)` by right invariance.

**Step 3.** For `l ∈ {a,b,c}` put `χ_u(a) = χ_u(c) = 1` and `χ_u(b) = −1`. The following move
sequences in `G` give `d(lul, u^(χ_u(l))) <= λ_l`, with `u = yxzxzy`:

```text
l = a:  ayxzxzya -> yaxzxzya -> yxazxzya -> yxzbxzya -> yxzxbzya -> yxzxzaya -> yxzxzyaa
        moves e2, e1, e3, e4, e3, e2:           λ_a = e1 + 2e2 + 2e3 + e4
l = c:  cyxzxzyc -> ybxzxzyc -> yxbzxzyc -> yxzaxzyc -> yxzxazyc -> yxzxzbyc -> yxzxzycc
        moves e5, e4, e3, e1, e3, e5:           λ_c = e1 + 2e3 + e4 + 2e5
l = b:  byxzxzyb -> ycxzxzyb -> yzczxzyb -> yzxcxzyb -> yzxzczyb -> yzxzxcyb -> yzxzxybb
        moves e5, e6, e6, e6, e6, e5:           λ_b = 2e5 + 4e6
```

The last words are `u`, `u` and `yzxzxy = u^(−1)`. So `μ := max_l λ_l <= 6ε`.

By induction on `n`, a word `w = l_1…l_n` satisfies

```text
d(w_G^(−1) u w_G, u^(χ_u(l_1)…χ_u(l_n))) <= λ_(l_1) + … + λ_(l_n).
```

For `w = w''l`, conjugating by `l` preserves distances, and
`d(l u^(±1) l, u^(±χ_u(l))) = d(lul, u^(χ_u(l)))`, since the second pair is the first pair or
its inverse. For `w = k'`, the sign is `(−1)^(#b(k'))` which is `1`, so

```text
d(u k'_G, k'_G u) = d(k'_G^(−1) u k'_G, u) <= (L+1) μ <= 6(L+1) ε.       (S3)
```

**Step 4.** Put `κ' = d(uδ', δ'u)`. Then

```text
κ' <= d(uδ', uk'_G) + d(uk'_G, k'_G u) + d(k'_G u, δ'u) <= 2 d(k_G, δ) + 6(L+1)ε.
```

**Step 5.** If `δ' = δ`, then `κ' = κ1`, and `(RL1)` of
`radu-mark-is-controlled-by-one-commutator` gives `d(δ^4,1) <= 2κ1 + 16ε`. If `δ' = δb`, then
`κ' = κ2`, and `(RL3)` gives `d(δ^4,1) <= 2κ2 + 36ε`. In both cases, by Steps 4 and 1,

```text
d(δ^4,1) <= 2κ' + 36ε
         <= 4 d(k_G,δ) + 12(L+1)ε + 36ε
         <= 4 d(γ_G,1) + (4L(r+1) + 12L + 48)ε
          = 4 d(γ_G,1) + (4L(r+4) + 48)ε.                                 ∎
```

## 3. Proof of (EB2)

Apply `(EB1)` to `π(a),…,π(z)`. All defects are 0, so `d(π(δ^4),1) <= 4 d(π(γ),1)` for every
`γ ∈ C ∖ {1}`. Every `g ≠ 1` fixing a vertex of `T_v` is `hγh^(−1)` with `γ ∈ C ∖ {1}`, and
`d(π(g),1) = d(π(γ),1)` by conjugation invariance. ∎

## 4. Fixing radius

**(a)** If `#c(γ)` is odd, `γ` moves `xo`, so `r = 0`. Otherwise `γ` fixes all neighbours of
`o`. Push `γ` through a single letter.
* **Through `y`:** the `V`-letter stays `y`, and the letters change by `a ↦ a`, `b ↦ c`, `c ↦ b`.
  So `σ_y(γ)` is `γ` with `b ↔ c` swapped, and `#c(σ_y(γ)) = #b(γ)`.
* **Through `x` or `z`:** the current `V`-letter toggles `x ↔ z` exactly when a `c` passes.
  * A letter passing `x` is unchanged, and a letter passing `z` has `a ↔ b` swapped.
  * The toggling positions are the same for both pushes, and the starting letters differ.
    So each occurrence of `a` or `b` in `γ` is swapped in exactly one of `σ_x(γ)`, `σ_z(γ)`.
  * Hence `#c(σ_x(γ)) = #c(σ_z(γ)) = #c(γ)`, which is even, and
    `#b(σ_x(γ)) + #b(σ_z(γ)) = #a(γ) + #b(γ)`.

By Lemma R, `r = 1` iff some neighbour section has `χ = −1`. With `#c(γ)` even, that happens iff
`#b(γ)` is odd.

Now let `L` be odd with `#b(γ)`, `#c(γ)` even. Then `#a(γ)` is odd, so `#b(σ_s(γ))` is odd for
some `s ∈ {x,z}`. Since `χ(σ_s(γ)) = 1`, `σ_(sy)(γ)` is `σ_s(γ)` with `b ↔ c` swapped, and it has
an odd number of `c`. So `r <= 2`, and `r = 2` by the two previous cases. For odd `L` the
constant is at most `4L·6 + 48`. ∎

**(b)** Let `v = s_1…s_n` be a minimizer of Lemma R, so `n = r`. Put `h_i = σ_(s_1…s_i)(γ)`.
* Each `h_i` has reduced length at most `L`, because it is represented by a pushed word of
  length `L`.
* `χ(h_i) = 1` for `i < n`, by minimality.
* `h_(i+1)` depends only on `(h_i, s_(i+1))`.

Suppose `(h_i, s_i) = (h_j, s_j)` for some `1 <= i < j <= n−1`. Then `s_1…s_i s_(j+1)…s_n` is
reduced, because `s_(j+1) ≠ s_j = s_i`. Along it the sections repeat those of `v` from index `j`
on, so it is a shorter candidate in Lemma R, which is a contradiction. So the pairs
`(h_i, s_i)`, `1 <= i <= n−1`, are distinct. They lie in a set of size `3N_+(L)`, so
`r <= 3N_+(L) + 1`. Also `N_+(L) <= 3·2^L − 2`, the number of reduced words of length at most
`L`, so `r <= 9·2^L`. ∎

**(c)** This is computation only. The artifact's section-automaton breadth-first search is
cross-checked against brute force on the balls for `L <= 7`, and the output lists the maxima.

## 5. Consequences

**(C1)** Two words for the same element of `Γ_R` differ, in the free product of six copies of
`C_2`, by a fixed product of `N` conjugates of relators. So their values differ by at most `Nε_n`.
* Write `g = hγh^(−1)` with `γ ∈ C ∖ {1}` reduced.
* The word `hγh^(rev)` has support `d_H(γ_n,1)`.
* By `(EB1)`, `4 d_H(γ_n,1) >= d_H(δ_n^4,1) − (4L(r+4)+48)ε_n`.

Take the `liminf`. ∎

**(C2)** Put `γ_G = 1` in `(EB1)`, then use 4(a). For odd `L`, `24L + 48 < m/ε` iff
`L < m/(24ε) − 2`. For odd `#c`, `r = 0` and `16L + 48 < m/ε` iff `L < m/(16ε) − 3`. ∎

**(C3)** The normalized Hamming lengths pass to a bi-invariant metric on `S_U`, so `(EB2)`
applies. For `g ≠ g'` in `hCh^(−1)`, `d(π(g),π(g')) = d(π(g^(−1)g'),1) >= m/4`. A uniformly
discrete subset of a metric space is closed, since a convergent sequence in it is eventually
constant. ∎

## 6. Calibration

**(K1)** `δ^2 ∈ Λ_v` by `(HK1)` of `radu-horizontal-projection-kills-delta-squared`. Since `Λ_v`
is normal, `yδ^2y ∈ Λ_v` and `w = [δ^2, yδ^2y] ∈ γ_2(Λ_v)`.
* **Nontrivial.** `w = xzxz·yxzxzy·zxzx·yzxzxy` is reduced of length 20, so `w ≠ 1` in `V`. The
  artifact checks this in normal form.
* **Hyperbolic on `T_v`.** Left multiplication by `w` fixes no vertex `vo`, since `V` acts simply
  transitively. It preserves the parity of `|v|`, so it has no inversion. A fixed-point-free
  automorphism of a tree without inversions is hyperbolic.
* **Trivial on `T_h`.** `w ∈ Λ_v`.

By item 4 of `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`,
`(xz)^4 ∉ γ_2(Λ_v)`. In `G_2` with the discrete metric, `d(δ^4,1) = 1` and `d(w,1) = 0`. ∎

**(K2)** `Q` is residually finite by item 1 of
`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`. Also:
* `C ∩ Λ_v = 1`. `C` is simply transitive on the vertices of `T_h = Γ_R/V`, because
  `Γ_R = CV` and `C ∩ V = 1`. An element of `C ∩ Λ_v` fixes the vertex `V`, so it lies in
  `C ∩ V = 1`.
* Choose finite quotients `q_j : Q → F_j` that are injective on the ball of radius `j`, and let
  `Γ_R` act on `F_j` through `q_j ∘ ρ` by left translation.
* These are homomorphisms, so every defect vanishes. `(xz)^4 ∈ Λ_v` by `(HK1)`, so the mark acts
  trivially.
* For fixed `g ∈ hCh^(−1) ∖ {1}`, `ρ(g) ≠ 1`, so `q_j(ρ(g)) ≠ 1` for large `j`. It then acts
  without fixed points, and `d_H(g,1) = 1`. ∎

**(K3)** The ball of radius `ℓ` in `C` has `3·2^ℓ − 2` elements. With
`ℓ = ⌈log_2 |C_n|⌉ + 1`, this exceeds `|C_n|`, so two distinct words of length at most `ℓ` have
the same image. The reduced form of `g^(−1)g'` is then a relation of length at most `2ℓ`.
* Two distinct permutations of `X_n` are at normalized Hamming distance at least `1/|X_n|`.
* The only proved radius bound is 4(b), which is exponential in `L`.
* So nothing forces `L_n(r_n+4)ε_n → 0`.

This is a limitation of the available bounds, not a theorem about models.
