# Referee report (gq-referee-a, proof-gap lens): K_2-stability for R_L, with its frame-complex, GE and K_1 inputs

**Reviewed** (lane gq-infinite-primes, marked urgent), read on origin/main:
- `leavitt-resolvent-k2-stability-holds`, with its `-proof` (eecdc0a2f);
- the three unreviewed inputs it rests on, each refereed here as well:
  - `leavitt-resolvent-frame-complex-is-highly-connected` (+ `-proof`, cb9fefa48);
  - `leavitt-ge-rings-have-stable-k1-at-rank-three` (+ `-proof`);
  - `leavitt-k1-stability-is-one-step` (+ `-proof`, 6035beb9a).

Khanh's text was read at `gq/src/on/2609.08428/khanh.tex`: the frame definitions (l.95–108), the leaf coordinates
(l.264–284), `lem:word-multiplier` (l.338–358), `prop:frame-cone` (l.360–391), `cor:frame-homology`,
`thm:raw-criterion` and its proof (l.430–495), and `lem:padded-centrality` (l.497–510).

**Verdict: PASS for all four.** There are six nits and no required fix.
- For the citation lens:
  - Brown's presentation theorem, used as Khanh derives it;
  - Menal–Moncasi GE (already pinned by referee b in AGP);
  - Voronetsky refinement;
  - `K_1(R_L) ≅ Z` on `[N+1]`.
- Together with the earlier PASSes, this gives:
  - `leavitt-surjective-k2-stability-implies-injective` and `leavitt-stabilization-kernels-are-one-step` (4ba142c64);
  - `leavitt-resolvent-stable-k2-class-is-computable` (8ffbfb9b4);
  - `leavitt-refinement-identifies-unstable-k2-levels` (items 2–4 in 2d373a8ea, item 1 by referee b).
- So I find no gap on the path to condition (i), `K_2` centrality, and a solvable word problem for `St_N(R_L)`,
  `N ≥ 3`.

## 1. `leavitt-k1-stability-is-one-step`
- **Item 1.**
  - `T(A⊕1)U = A ⊕ I_2`, because the split block of `1` is `[[e*e, e*f],[f*e, f*f]] = I_2`.
  - `α_(n+1)` is an isomorphism with `α(E_(n+1)) = E_(n+2)`, so it is bijective on classes. Hence
    `ker(s_(n+1)s_n) = ker s_n`, and by induction this is `ker(GL_n/E_n → K_1)`. ✓
- **Item 2.**
  - `TE = ι`, the inclusion of the first `n` coordinates, because `e*e = 1` and `f*e = 0`. And `E*U = π`, the
    projection, because `e*(e, f) = (1, 0)`.
  - So `α_n(EAE*) = A ⊕ 0`, and `T(1−EE*)U = T·diag(0,…,ff*)·U = 0 ⊕ 1`. That gives `α_nτ_e = s_n`.
  - `τ_e` is multiplicative, because `E*E = 1` and `E*(1−EE*) = 0`. It sends `t_ij(a)` to `t_ij(E_ii a E*_jj)`, so it
    preserves `E_n`.
  - `ue = u(ee*)e = eee*e = ee`, so `UE = E²`, and both `Uτ_e(A)U*` and `τ_e²(A)` equal `E²AE*² + 1 − E²E*²`. ✓
- **Item 3.**
  - Surjectivity of `s_n`, together with `α_n(E_n) = E_(n+1)`, puts every left coset in the form `τ_e(A')E_n`.
  - With `H = τ_e(A')X`: `τ_e(H) ∈ E_n` forces `c_U(τ_e A') ∈ E_n`, hence `τ_e(A') ∈ E_n`, hence `H ∈ E_n`.
  - Normality of `E_n` is not needed: `s_n(g_1E) = s_n(g_2E)` gives `(g_1^(−1)g_2) ⊕ 1 ∈ E_(n+1)`, so trivial kernel
    already gives injectivity on left cosets. ✓

## 2. `leavitt-ge-rings-have-stable-k1-at-rank-three`
- **Items 1–3.**
  - The diagonals normalize `E_n`, and `diag(a,b) = diag(ab,1)·W(b^(−1))W(−1)`. So every class contains
    `diag(u,1,…)`, `s_n` is onto for `n ≥ 1`, and, with §1, bijective for `n ≥ 3`.
  - Under GE, `GL_n = E_nD_n`, so `E_n` is normal and `GL_n/E_n` is a group `≅ Z` on `[N+1]`. ✓
- **Item 4, compression (the author asked about this).**
  - *Refinement.* `s_μbt_ν = s_(μ1)b(N+1)t_(ν1) + s_(μ2)b(0)t_(ν2)` is exactly `ψ(b) = diag(b(N+1), b(0))`.
  - *Coefficients are recovered.* At a common level `(L+d, L)`, `Y_(αβ) = t_α x_d s_β`, so `x_(d_0) ≠ 0` gives some
    `Y ≠ 0`.
  - *The shape of `z_0`.* With `|β| = |β_0|`, `t_βs_(β_0) = δ`, and `t_(α_0)s_α` is `δ`, a `t_a`, or an `s_b`, as stated.
  - *The tagged vacuum.* `gv = vg(k)` from `gs_1^k = s_1^kg(N+k)` and `g(N+k)s_2 = s_2g(k)`.
  - *The prefix argument (the author asked about this).* Let `1 ≤ |a| ≤ m`. In `aw = a·1^k2·1^m2`, the first `2` of the
    copy of `w` sits at position `|a| + k + 1`, which lies in `[k+2, k+m+1]`. In `w` those positions are all `1`s. So
    `w` is never a prefix of `aw`, and likewise never of `bw`.
  - So `v*z_0v = Y(k) ≠ 0`. ✓ See N6.

## 3. `leavitt-resolvent-frame-complex-is-highly-connected`
- **Item 1, the simultaneous multiplier (the author asked about this).**
  - Item 4 of §2 gives `t_(α_0w)a_ix'_i = 1`, with `c^(−1)` central and absorbed into `x'_i`.
  - *Cross terms.* In `t_2t_1^(M_i)·s_αgt_β·s_1^(M_j)s_2`:
    - `t_1^(M_i)s_α ≠ 0` only for `α = 1^(|α|)`, and `t_βs_1^(M_j) ≠ 0` only for `β = 1^(|β|)`. This needs
      `M_i, M_j ≥ D` (N4).
    - `gs_1^bs_2 = s_1^bs_2g(b)`, and `t_2t_1^as_1^bs_2` equals `1` if `a = b` and `0` otherwise, since
      `t_1s_2 = 0 = t_2s_1`.
    - So the cross terms vanish when `|M_i − M_j| > D`. ✓
- **Item 2 (the author asked whether Khanh's frame-cone proof uses anything else).** I read l.360–391 line by line.
  The proof uses exactly:
  - the leaf maps `L_q`;
  - `End(R_R) =` left multiplications, so `ρ_iΦ = a_i·`;
  - `a_i ≠ 0`;
  - the multiplier `η_i^*a_ix = 1`, with each `η_i` nonempty;
  - the sibling kernel `ker η^* = ⊕s_ℓR`, from a complete prefix code.

  Nothing depends on characteristic 2. Only the multiplier lemma (l.338ff) uses `F_2` coefficients. ✓
- **Item 3.** The cone operator `h_v` of `cor:frame-homology`, and Khanh's triangular fan for `r ≥ 4`, since edges
  have `2 ≤ r − 2` vectors. ✓
- **Item 4, `E_r`-transitivity (the author asked about this).**
  - A completion `g ∈ GL_r` exists.
  - Adjust by `diag(I_k, (N+1)^m, 1, …)` on a complement coordinate, which is nonempty since `k ≤ r − 1`.
  - `GL_r/E_r ≅ Z` is an abelian group, so conjugation by permutations acts trivially on it, and the position of the
    entry does not matter.
  - The first `k` columns are unchanged. ✓

## 4. `leavitt-resolvent-k2-stability-holds`
- **Point 1: `J` and `K` (the author asked about this).**
  - The vertex `b_1` is the vector `e_1`, so `J = {g ∈ E_n : ge_1 = e_1} = {j(b,H)}`.
  - `j(b,H) = diag(1,H)x_1(b)` (N2), so `j(b,H) ∈ E_n` iff `diag(1,H) ∈ E_n`. Its class is `[H]`, and injectivity at
    `n−1 ≥ 4` gives `H ∈ E_(n−1)`.
  - In the same way, the edge stabilizer has `H ∈ E_(n−2)`, with `n−2 ≥ 3`. ✓
- **Point 2: `P_12 ∈ E_n`, and the Borel presentation (the author asked about this).**
  - `diag(−1,1) = diag([a,W],1)` lies in `E_2` by Khanh's identity, since `[a,W] = −1`. So `P_12, P_23 ∈ E_n`, which
    also shows `[−1] = 0` directly (N1).
  - Khanh's derivation (l.450–468) uses the following:
    - one orbit on ordered 1-, 2- and 3-frames;
    - cell stabilizers fixing their ordered vertices, with no inversions, since `(u,v) ≠ (v,u)`;
    - `Tb_1 = b_2`, `Tb_3 = b_3`, `h ∈ J` and `hb_2 = b_3`;
    - simple connectivity.
  - All of these hold for `E_n` acting on `X_n(R_L)`, `n ≥ 5`. `T² = 1` is derived inside `Π`, as Khanh notes. ✓
- **Point 3: the exact Weyl lift (the author asked about this).**
  - `a² = W² = 1`, and `WaW = (fe* − ef*)(ef* + fe*) = ff* − ee* = −a`, so `[a,W] = aWaW = −1`.
  - *Exactness for `k ≥ 3`.* `w_12(u)X_1k(c)w_12(u)^(−1) = X_2k(−u^(−1)c)` holds in any ring. I recomputed the
    successive conjugates by `x_12(u)`, `x_21(−u^(−1))` and `x_12(u)`.
  - *Exactness on `X_12` and `X_21`.* It follows from `X_12(c) = [X_13(c), X_32(1)]`. This gives
    `h_12(u)X_12(c)h_12(u)^(−1) = X_12(ucu)`, and similarly for `X_21`, for arbitrary units.
  - So `d_1` acts on every generator exactly as `diag(−1,1,…)` does, and `ω_12 = w_12(1)d_1` acts by the index
    permutation with no signs. I checked the four cases `X_1k`, `X_2k`, `X_k1` and `X_k2`, and `X_12 ↦ X_21`.
  - `ω_12` is a word in `X_12, X_21`, so it commutes exactly with every `X_kl`, `k, l ≥ 3`. ✓
- **Point 4: the relations modulo `C` (the author asked about this).**
  - `C` is central by `lem:padded-centrality`, whose proof (l.500–509) holds for any unital ring.
  - Any lift of a permutation, signed or not, carries the coordinate copy of `K_2(n−1)` onto another coordinate copy.
    So every copy equals `C` (N3).
  - `ℓ` and `ℓ_0` are well defined modulo `C`.
  - The row identity is exact: the row group is abelian, and generators act through their matrices.
  - The edge relation holds exactly, since `x_1(b)` and `x_2(a)` commute.
  - The triangle quotient and `ω_12²` are words on `{1,2,3} ⊆ {1,…,n−1}` lying in `K_2(n)`. Since
    `E_(n−1) → E_n` is injective, they lie in `j(K_2(n−1)) = C`. ✓
- **Point 5: surjectivity and the deduction (the author asked about this).**
  - The image of `ψ` contains `X_ij` for `i,j ≥ 2`, `X_1j`, and the conjugates `X_i1` and `X_21` under `ω_12`.
  - `φ̄ψ = p` is an isomorphism and `ψ` is onto, so `ψ` is bijective and `K_2(n) = C` for `n ≥ 5`. That is
    surjective stability at `m = n − 1 ≥ 4`.
  - Then e73333e45 item 2 gives `U_m = 1`, refinement gives `U_3 ≅ U_4`, and the computable-class section gives
    surjectivity onto `K_2(R_L)`.
  - Centrality transports to `N = 3, 4` through `D`. ✓

## Nits
- **N1 (K_2 proof, Step 0).** `diag(−1,1,…) ∈ E_m` follows at once from `[a,W] = −1` and Khanh's commutator identity.
  Citing Step 2 there avoids routing the fact through `K_1`.
- **N2 (K_2 proof, Step 1).** `j(b,H)` equals `diag(1,H)·x_1(b)`. The product `x_1(b)·diag(1,H)` is `j(bH, H)`. This
  does not affect membership, and Step 3's `σ(j(b,H)) = ℓ(H)x_1(b)` already uses the correct order.
- **N3 (K_2 proof, (Z)).** The equality "every coordinate copy of `K_2(n−1)` is `C`" does not need exact lifts. Any
  lift `ω` of the permutation carries one copy onto the other and fixes `C`, because `C` is central. As written, Step 0
  uses Weyl words before Step 2 constructs them.
- **N4 (frame node, item 1).** Require `M_i ≥ D` as well as `|M_i − M_j| > D`. That is what makes `t_1^(M_i)s_α` and
  `t_βs_1^(M_j)` reduce as stated.
- **N5 (frame node, "Consequence").** The sentence that the characteristic-0 presentation "needs one more relation"
  because `T² = diag(−1,−1,…)` is superseded. The K_2 proof takes `T = P_12 ∈ E_n` with `T² = 1`. Update or delete it.
- **N6 (GE node, item 4).** The case split "`a = 1^j` with `j ≤ k`" is unnecessary. The position-`(|a|+k+1)` argument
  covers every `a` with `1 ≤ |a| ≤ m`.
