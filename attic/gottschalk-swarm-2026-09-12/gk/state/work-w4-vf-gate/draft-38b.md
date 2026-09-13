
### 38.3 No rank-null closing (Section 3). PASS

- **Proposition 3.1, recomputed.**
  - **Hamming.** `j` sends `prod_U Mon_(m_n)(F_q)` to `prod_U Sym(X_(m_n))`, where rank-null is Hamming-null
    (`monomial-rank-models-are-hamming-models`, ESTABLISHED, factor two). The null subgroup is normal, so the
    composite `π_1(Y_hex) -> prod_U Sym / null` kills `<<t>>`. It factors through `G`, nontrivially on `x_12(1)`.
  - **Binary.** The kernel is a proper normal subgroup of the simple `G`, so it is trivial. `G` embeds in a universal
    sofic group and is sofic (Elek–Szabó), which contradicts `openai-leavitt-unit-nonsofic`.
  - **Ternary.** The kernel `N` misses `x_12(1)`, so `NZ != G` by the argument of Lemma 2.2. Hence `N ⊆ Z`, and the
    image is `G` or `G/Z`.
    - `G` is nonsofic by `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
    - `G/Z` is nonsofic by `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`. Alternatively, a sofic `G/Z`
      with `Z` finite would make `G` sofic (amenable extension).
  - **Coverage.** A Theorem 1.1 model is monomial (permutation matrices). `x_12(1)` has order `p` and acts freely, so
    `rk(σ(x_12(1)) − 1) = (p − 1)/p > 0`.
- **Corollary 3.2, recomputed.**
  - **The letter.** A permutation `π` has `rank(π − I) = |supp π| − (number of nontrivial cycles) >= |supp π|/2`.
    So `rank(π − I)/m < 1/k` gives `|supp π|/m < 2/k`, and `d_H(π a π^-1, a) <= 2|supp π|/m < 4/k`.
  - **Relators.** At the stage, vertex relations and forest identifications hold exactly. Each use of `e_6` costs at
    most `4/k`, since `d_H` is bi-invariant. So every relator holds up to `4L/k`, and `w` is within `4L/k` of the
    free permutation `λ(x_12(1))`.
  - **The limit.** Over `k`, the ultraproduct satisfies the relators exactly, which gives `G -> prod_U Sym / null`
    with `x_12(1)` at Hamming distance `1` from the identity. Proposition 3.1 excludes it.
  - **Uniformity.** `S`, `Q`, `w`, `D` and `L` are fixed before any model is chosen, so `ε_p` is uniform. For `p = 3`
    the models are those of 38.4.

### 38.4 Calibrations, ternary transfer and the rank-two kernel (Sections 4–6). PASS

- **Calibrations, recomputed.**
  - `|SL_3(F_2)| = 168 = 8 · 21` and `|SL_3(F_3)| = 26 · 24 · 18/2 = 5616 = 27 · 208`. The regular representation
    restricts to free actions of the `U_π(F_p)` that agree literally on every edge. So `σ(t) = 1` and `σ` is
    nontrivial.
  - `R_0`: each stage piece lies in the finite `GL_(3·2^k)(F_2)`, whose regular representation closes the stage.
    `EL_3(R_0)` is the union of the simple groups `SL_(3·2^k)(F_2)`, so it is infinite and simple but not finitely
    generated.
  - `F_2[x]`: `SL_3(F_2[x]/(f))` are finite quotients.
  - UT₄: a perfect group has no nontrivial nilpotent image.

  Each calibration closes the hexagon. None makes a rank model trivial.
- **Ternary transfer (Section 5), re-derived here.** Every step of the firewall's Theorem 1.1 (lines 53–95 there) is
  independent of the field:
  - `|H_(n,w)|` divides `N_n`, and free actions of one finite group on equal sets are isomorphic;
  - the orbit matching for letters;
  - `F_p[Ω_n] ≅ F_p[Q]^(N_n/|Q|)`, and the fixed-vector bound `1/|H_(m,v)|`;
  - `rank(I − AB) = rank(I − BA)` over a field.

  `U_π(L_(F_3)(1,2))` is countable and locally finite by the span argument of Section 34 with `F_3`-spans. So the
  `F_3` model exists with `M = prod_U M_(m_n)(F_3)`.

  The root-pair pieces: `[x_ij(ua), x_jk(vb)] = x_ik(uv ab)` is central, so the order is at most `27`. Since
  `(a, b, c)^3 = (3a, 3b, 3c + 3ab) = 1`, the exponent is `3`. Sections 2–3 for `p = 3` are conditional as the host
  theorem is.
- **Rank-two kernel.**
  - `(i,j)` and `(j,i)` are positive on complementary arcs, so no `U_π` contains opposite roots.
  - Over `F_2`, `[[1,1],[0,1]] [[1,0],[1,1]] = [[0,1],[1,1]]`, whose cube is `I`. So `ω -> 1` in `E_3(R)`, and in `G`
    by Section 34.
  - `x_12(1)` and `x_21(1)` lie outside `E_1 = <x_13(R), x_23(R)>`. So `ω` is a reduced alternating word of length
    `6` in `U_123 *_(E_1) U_213`, which embeds in the tree amalgam `P`. Hence `ω != 1` in `P`.
  - The `F_2` calibration kills `ω` at every stage.
