# L²-acyclicity of unit groups of Leavitt path algebras with trivial unit class, 2026-09-12

Lane `ex-lueck-approximation`. Addendum to `research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md`,
whose Theorem A (frame criterion) is used unchanged. Status: proved on paper, unreviewed.

**Theorem F.** Let `K` be a field and `E` a finite graph with no sinks, cofinal, satisfying
condition (L). Put `L = L_K(E)` and suppose `[1_L] = 0` in `K_0(L)`. Then every L²-Betti number of
`L^x` vanishes. If `char K = p > 0`, `L^x` is nonsofic.

## 1. Inputs

- (AAP) `L` is purely infinite simple: Abrams--Aranda Pino, arXiv:math/0509496, Theorem 11, whose
  conditions are no nontrivial hereditary saturated sets, condition (L), and every vertex connecting
  to a cycle. For a finite sinkless graph:
  - every vertex connects to a cycle, since every long enough path repeats a vertex;
  - cofinality excludes nontrivial hereditary saturated sets (derivation in
    `leavitt-path-algebras-purely-infinite-simple-criterion`).
- (AGP) Nonzero finitely generated projective `L`-modules with equal `K_0` classes are isomorphic:
  Ara--Goodearl--Pardo Proposition 2.2, through `purely-infinite-leavitt-path-v-monoid-cancellation`.
- (B) Simultaneous strong division, `leavitt-path-algebras-have-simultaneous-strong-division` (the
  path-host lane's claim; Theorem B of `bh-leavitt-path-steinberg-hosts-2026-09-12`): for nonzero
  `a_1..a_s` there are `X` and `u_i` with `u_i a_i X = 1`.

## 2. Consequences of `[1] = 0`

1. `[L ⊕ L] = 2[1] = 0 = [1]`, so `L ⊕ L ≅ L` by (AGP). An isomorphism `L -> L ⊕ L` is left
   multiplication by a column `(f_0, f_1)^T` with a left inverse row `(e_0, e_1)`. That gives a
   unital Leavitt family `e_i f_j = δ_ij`, `f_0 e_0 + f_1 e_1 = 1`. Hence:
   - there is a unital homomorphism `L_K(1,2) -> L`, injective because `L_K(1,2)` is simple
     (`leavitt-algebras-l-k-1-n-are-simple`);
   - complete prefix codes give ring isomorphisms `M_r(L) ≅ L`, so `GL_r(L) ≅ L^x` for every `r`.
2. For `y in L` with a left inverse `u` (`u y = 1`), `L = yL ⊕ ker(u ·)` and `yL ≅ L`. So
   `[ker u] = 0`. If `ker u != 0`, then `ker u ≅ L ≅ L^m` for every `m >= 1`, by (AGP) and item 1.
3. **Nonzero kernels.** Given `X, u_i` from (B) with `u_i a_i X = 1`, put `X' = X f_0` and
   `u'_i = e_0 u_i`, with `e_0, f_0, f_1` from item 1.
   - `u'_i a_i X' = e_0 (u_i a_i X) f_0 = e_0 f_0 = 1`.
   - `ker(u'_i ·) = {z : e_0 (u_i z) = 0} ⊇ {z : u_i z in f_1 L}`, because `e_0 f_1 = 0`. This contains
     `a_i X f_1`, since `u_i a_i X f_1 = f_1`, and `a_i X f_1 != 0` because `u_i (a_i X f_1) = f_1 != 0`.
   - So `ker(u'_i ·) != 0`, and by item 2 it is `≅ L`.

## 3. Frame connectivity over `L`

Khanh's Proposition 4.2 transfers.
- Given frames `W_i` with completions `L^r = W_i ⊕ C_i`, `C_i ≅ L^(q_i)`, `q_i >= 2`, compose the
  quotient coordinates with the leaf isomorphism `L^(q_i) ≅ L` to get `ρ_i : L^r -> L` with kernel
  `W_i` and section `σ_i`.
- `ρ_i Φ` is left multiplication by some `a_i != 0`, where `Φ : L ≅ L^r` is a leaf isomorphism.
- Apply (B) and Section 2, item 3, to get `X'` and `u'_i`. Put `v = Φ X'` and
  `y_i = ρ_i v = a_i X'`, so that `u'_i y_i = 1`.
- Khanh's (4.3)--(4.4) use only `u'_i y_i = 1` and give `L^r = W_i ⊕ vL ⊕ σ_i ker u'_i`.
- By Section 2, items 2 and 3, the complement `vL ⊕ σ_i ker u'_i ≅ L^(q_i)` splits off
  `σ_i ker u'_i ≅ L^(q_i - 1)`. So `v` extends every frame of the family to a simplex of `X_r(L)`,
  with a nonzero complement of the right formal size.
- Khanh's coning proof of Corollary 4.3 then gives `H̃_d(X_r(L); Z) = 0` for `0 <= d <= r-3`.

## 4. Proof of Theorem F

- `L` is infinite: paths are linearly independent, and a cycle gives infinitely many.
- Theorem A at `r = n + 3`, together with `GL_r(L) ≅ L^x`, gives `β_n^(2)(L^x) = 0`.
- If `char K = p`, then `L_(F_p)(1,2) ⊆ L_K(1,2) ⊆ L` (item 1), so `L^x` contains the nonsofic
  `L_(F_p)(1,2)^x` (`d-ary-leavitt-groups-nonsofic-over-finite-fields`). ∎

**Example.** The two-vertex graph with `N_E = [[2,3],[1,2]]` over `F_2` has `K_0 = Z/2` and
`[1] = 0` (`bh-leavitt-path-steinberg-hosts-2026-09-12`, Section 1). Its unit group is L²-acyclic
and nonsofic, and its host ring is not isomorphic to `L_2`.
