---
rg: 2
id: minimal-sfts-have-no-finite-asymptotic-pairs-proof
kind: route
title: Flip one asymptotic pair independently at a separated syndetic set of occurrences, avoid one pattern by the local lemma, and contradict minimality
target: minimal-sfts-have-no-finite-asymptotic-pairs
requires: [minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs]
---

The notation is that of the target. The graph requirement is used only for part 2 (its part 3,
the equivalence of no finite asymptotic pair with boundary determinism, which holds for every
SFT over every group and uses no (NZ) hypothesis). Part 1 is self-contained. Imported:
- **Symmetric Lovász local lemma** (Erdős–Lovász 1975; e.g. Alon–Spencer, *The Probabilistic
  Method*, Cor. 5.1.2). Let `A_1, ..., A_N` be events in a probability space. Suppose each
  `A_i` is mutually independent of all but at most `Δ` of the others, `Pr(A_i) <= p` for all
  `i`, and `e p (Δ + 1) <= 1`. Then `Pr(no A_i occurs) > 0`.
- `β(a + b) <= β(a) β(b)`, since `B_(a+b) = B_a B_b` for word length.

Suppose `X` is minimal and `x ≠ x'` is a finite asymptotic pair. Put `E = Δ(x, x') ≠ ∅`,
`D = E B^2`, and fix `ρ` with `D ∪ B ⊆ B_ρ`. Fix `e_0 ∈ E`. Say `y` *has `p` at `g`* if
`y(gd) = x(d)` for all `d ∈ D`.

## 1. Independent flips

**Lemma 1.** Let `y ∈ X`, and let `Q ⊆ Λ` be a set of positions at which `y` has `p`, with
`d(g, g') > 2ρ` for distinct `g, g' ∈ Q`. For `S ⊆ Q` define `y_S` by `y_S(ge) = x'(e)` for
`g ∈ S`, `e ∈ E`, and `y_S = y` elsewhere. Then:
1. `y_S` is well defined and lies in `X`;
2. for `g ∈ Q`, `y_S(g e_0) = x'(e_0)` if `g ∈ S` and `y_S(g e_0) = x(e_0)` if `g ∉ S`;
3. `y_S|_F` depends only on `S ∩ {g ∈ Q : gE ∩ F ≠ ∅}`, for every `F ⊆ Λ`.

*Proof.* If `gd = g'd'` with `d, d' ∈ D`, then `|g^(-1)g'| = |d d'^(-1)| <= 2ρ`. So the sets
`gD`, `g ∈ Q`, are pairwise disjoint, and `y_S` is well defined. Parts 2 and 3 follow, because
`y_S` differs from `y` only on `∪_(g ∈ S) gE` and `y(g e_0) = x(e_0)`.

For part 1 take `k ∈ Λ`.
- If `kB` meets no `gE` with `g ∈ S`, then `y_S = y` on `kB`, and the window is allowed.
- Otherwise `kb = ge` with `g ∈ S`, `b ∈ B`, `e ∈ E`. Then `g^(-1)k = eb^(-1) ∈ EB`, so
  `kB ⊆ gEB^2 = gD`.
  - Since `gD` is disjoint from every `g'D ⊇ g'E` with `g' ≠ g`, on `gD` the point `y_S` is
    `y` changed on `gE` only.
  - For `d ∈ D`: if `d ∈ E` then `y_S(gd) = x'(d)`; if `d ∉ E` then
    `y_S(gd) = y(gd) = x(d) = x'(d)`.
  - So `y_S(kc) = x'(g^(-1)kc)` for `c ∈ B`, that is
    `(k^(-1).y_S)|_B = ((g^(-1)k)^(-1).x')|_B ∈ W`.

Hence `y_S ∈ X`. ∎

## 2. Syndetic occurrences

**Lemma 2.** There is `L` such that every `y ∈ X` has `p` at some point of every ball `hB_L`.

*Proof.* `C = {y ∈ X : y|_D = x|_D}` is clopen and contains `x`, and `y` has `p` at `g` iff
`g^(-1).y ∈ C`. `U_n = ∪_(g ∈ B_n) g.C` is open and increasing in `n`, and
`∪_n U_n = ∪_g g.C` is a nonempty open invariant set, so its complement is a closed invariant
proper subset, empty by minimality. By compactness `X = U_L` for some `L`. For `h ∈ Λ` and
`y ∈ X`, apply this to `h^(-1).y`: some `g ∈ B_L` has `g^(-1)h^(-1).y ∈ C`, so `y` has `p` at
`hg ∈ hB_L`. ∎

## 3. A separated syndetic set

Fix `y ∈ X`. Let `O` be the set of positions at which `y` has `p`. Enumerate `O` and choose
greedily a maximal `Q ⊆ O` with pairwise distances `> 2ρ`. Every `o ∈ O` is within `2ρ` of
`Q`, so by Lemma 2 every ball `hB_K`, `K = L + 2ρ`, meets `Q`.

**Lemma 3.** For every `h` and every `N >= 0`, `|Q ∩ hB_(N+K)| >= β(N) / β(2K)`.

*Proof.* Choose a maximal `Y ⊆ hB_N` with pairwise distances `> 2K`. The balls `yB_K`,
`y ∈ Y`, are pairwise disjoint, lie in `hB_(N+K)`, and each meets `Q`. By maximality
`hB_N ⊆ ∪_(y ∈ Y) yB_(2K)`, so `β(N) <= |Y| β(2K)`. ∎

## 4. Avoiding one pattern

Fix `N`, to be chosen, and put `R = N + K + ρ` and `P = y|_(B_R)`, a pattern that occurs in
`X`. For `S ⊆ Q` and `h ∈ Λ` let `A_h` be the event `(h^(-1).y_S)|_(B_R) = P`, that is
`y_S(hb) = y(b)` for `b ∈ B_R`.

- **Probability.** Let `S` be random, each `g ∈ Q` in `S` independently with probability 1/2.
  Let `Q_h = Q ∩ hB_(N+K)`. For `g ∈ Q_h`, `|h^(-1) g e_0| <= N + K + ρ = R`, so
  `g e_0 ∈ hB_R`. On `A_h`, part 2 of Lemma 1 reads off `[g ∈ S]` from
  `P(h^(-1) g e_0) = y_S(g e_0)`, because `x(e_0) ≠ x'(e_0)`. So `A_h` forces `S ∩ Q_h` to be one
  specific set, and `Pr(A_h) <= 2^(-|Q_h|) <= 2^(-β(N)/β(2K))` by Lemma 3.
- **Dependence.** By part 3 of Lemma 1, `A_h` is determined by the coins at
  `{g ∈ Q : gE ∩ hB_R ≠ ∅} ⊆ hB_(R+ρ)`. Events determined by disjoint sets of independent coins
  are mutually independent. Two such coin sets meet only if `d(h, h') <= 2R + 2ρ`. So each
  `A_h` is mutually independent of all `A_(h')` but at most
  `Δ = β(2R + 2ρ) <= β(N)^2 β(2K + 4ρ)` of them.
- **Choice of `N`.** `Λ` is infinite and finitely generated, so `β(N) -> ∞`, and
  `e · 2^(-β(N)/β(2K)) · (β(N)^2 β(2K + 4ρ) + 1) -> 0`. Fix `N` with this at most 1.

For each finite `F ⊆ Λ` the events `A_h`, `h ∈ F`, involve finitely many coins, and the local
lemma gives `S_F ⊆ Q` for which no `A_h`, `h ∈ F`, holds.

**Compactness.** Take finite `F_1 ⊆ F_2 ⊆ ...` exhausting `Λ`. A subsequence of `S_(F_n)`
converges in `{0,1}^Q` to some `S`. Each `A_h` depends on finitely many coins, so it fails for
`S`, since it fails for `S_(F_n)` once `h ∈ F_n` and `S_(F_n)` agrees with `S` on those coins.

## 5. Contradiction

`y_S ∈ X` by Lemma 1, and no `h` has `(h^(-1).y_S)|_(B_R) = P`. So the orbit of `y_S` misses the
nonempty open set `{z ∈ X : z|_(B_R) = P}`, which contains `y`. This contradicts minimality.
Hence `X` has no finite asymptotic pair, which is part 1. Part 2 is part 1 combined with part 3
of `minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs`. ∎

## Remarks

- No group-ring condition is used. The (NZ) descent certifies only that no *linear* potential
  separates `p` from `p'`. The proof here uses the full product structure of the independent
  flips instead of one potential, so torsion (`a = 1 + t`, `ν = 1 - t`) no longer matters.
- Only the one-point statement "the orbit of `y_S` is dense" is contradicted; freeness of the
  action is not used.
