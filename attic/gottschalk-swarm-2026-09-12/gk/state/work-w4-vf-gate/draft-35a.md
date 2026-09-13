
## 35. w7-sub-multiletter (37bafd8f30)

Sources:
- Artifact `multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md` (blob `71cb2271`), Sections 0–6.
- The OPEN claims `split-cylinder-data-cannot-force-defect-submultiplicativity` (blob `7a134bb1`) and
  `lex-decreasing-units-with-order-preserving-letters-are-amenable` (blob `99448841`).
- The routes `split-cylinder-data-defect-firewall-proof` (blob `10ba7520`) and
  `lex-decreasing-units-order-preserving-letters-amenability-proof` (blob `10e58dd6`).

**Verdict: PASS on Sections 2–5, both claim displays and both routes, with one CORRECTION to Lemma 6.1 (35.4).**
- The literal hypothesis of Lemma 6.1 is too weak, and its first conclusion is false: an explicit order preserved by
  `b` makes every positive root move points strictly one way, but not all the same way.
- The lemma is correct when the positive roots of each frame move one common way, and that is all the mechanism of
  Theorem 3.5 needs. Nothing in either claim statement depends on the literal version. The scope sentence of the lex
  claim needs "in one common direction".

It is decision-level for the SUB plans:
- a relation-only deficit from `Gamma_2(R^x)` would be the gate itself;
- one from `U_< ⋊ F` would prove `F` nonamenable.

Nothing here proves that rank models are trivial. `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, the
gate and Plan 1 stay OPEN.

### 35.1 Cylinder swaps (Section 2). PASS

- **Lemma 2.1, recomputed.** Incomparable `A`, `B` give `T[B]S[A] = 0 = T[A]S[B]`. So
  - `tau S[A] = S[B] + S[A] − e_A S[A] = S[B]`, and `T[A] tau = T[B]`;
  - `tau e_A tau = S[B]T[B] = e_B`, which conjugates `iota_A(g)` to `iota_B(g)`.
  - As a partial-map sum, `tau` exchanges `[A]` and `[B]` and fixes the finite union of cylinders
    `X ∖ ([A] ∪ [B])`. So it is an involution in `V`.
- **Lemma 2.2, recomputed.**
  - Disjoint supports give `iota_A(g) iota_B(h) = S[A]gT[A] + S[B]hT[B] + 1 − e_A − e_B`, which is symmetric.
  - Compressing `prod iota_(A_i)(g_i)` by `T[A_j] · S[A_j]` returns `g_j`, so `G^k` is faithful.
  - `pi -> sum S[A_(pi i)]T[A_i] + 1 − sum e_(A_i)` is an injective homomorphism `S_k -> V`, and it sends
    transpositions to the swaps.
  - The kernel `K` of `G wr S_k -> Gamma_k(G)` is normal and meets the normal subgroup `G^k` trivially, so it
    centralizes `G^k`.
  - An element with `pi(i) != i` sends `iota_(A_i)(a)`, `a != 1`, into another slot. So `K <= G^k`, and `K = 1`.
- **Proposition 2.3, recomputed.**
  - `P_pi (Y_1 (x) ... (x) Y_k) P_pi^(−1)` moves slot `i` to slot `pi(i)`. So `sigma_n(x) sigma_n(y)` and
    `sigma_n(xy)` differ slotwise by `rho_n(g_i) rho_n(h') − rho_n(g_i h')`.
  - `rk(X (x) Y − X' (x) Y') <= rk(X − X') rk(Y) + rk(X') rk(Y − Y')`, with normalized ranks at most `1`, gives the
    sum bound. So `sigma` is an asymptotic homomorphism.
  - `sigma_n(D_(A_i))` is `D_rho` in slot `i`, exactly at every stage. A product over distinct slots has normalized
    rank `delta_(rho_n)^m`, and the limit is `delta_rho^m`.
  - The joint fixed space of `(rho_n(s) − 1) (x) 1`, `s in S`, is `ker(col_S) (x) (rest)`, of normalized rank
    `f_(rho_n)(S)`. In the ultraproduct `Fix(sigma(Gamma_k))` lies inside it for every finite `S`, so the fixed rank
    is at most `f_rho`.
- **Corollary 2.4.** With `k = m = 2`, `delta^2 <= theta delta^2` forces `delta = 0`.
  - Sofic `G` with an element of infinite order: Theorem S gives `delta = 3/8`, and `G wr S_2` is sofic.
  - Finite `G`: `Gamma_k(G)` is finite.
  - `G = R^x`: incomparable words are nonempty, so `[A]` is a proper cylinder. The gap gives `delta >= c_0` in every
    nontrivial fixed-point-free model, so `delta = 0` means every model is trivial, and in particular the gate holds.
    This is a conditional firewall. It does not assert that models are trivial.
- **Characteristic three.** `iota_A(−1) = 1 + e_A`. When `[A] ∪ [B] = X`, `iota_A(z) iota_B(z) = 1 − 2 = −1 = z` goes
  to `(−1) (x) (−1) = +1`. When the union is proper, every element of `Gamma_2(G)` is `1` on the complementary
  corner, so `z` is not in `Gamma_2(G)` and `<z> x Gamma_2(G)` takes an anti-central model.
- **Scope.** `x_0` sends `[10]` onto `[01]` and `[11]` onto `[1]`, so it is not a single prefix replacement per
  cylinder. That is correct.

### 35.2 The lexicographic Borel group (Section 3). PASS

- **Lemma 3.1, recomputed.** In the case `v' = wu`, `w'` is a prefix of `w` is impossible, since then
  `[wu] ⊆ [w']`. So `[w'] ⊆ [w]`, or `[w] < [w']`, and either way `[vu] ⊆ [v] < [w']`. The case `w = v'u` is the
  mirror image.
- **Lemma 3.2, recomputed.**
  - The ranges of `P_k` are nested nonempty compact sets.
  - The pullbacks `eta_j` increase strictly, and every length-`n` prefix is eventually constant.
  - For `j` large, `m_j = S[v]T[w]` has `v` a prefix of `eta_(j−1)` and `w` a prefix of `eta_j`. Both agree with
    `eta_inf` beyond length `L`, so `v` and `w` are comparable, which contradicts `[v] < [w]`.
- **Corollary 3.3.** `N` is finite over `F_2`, the inverse is a finite geometric sum, and `(1 + n)^(2^r) = 1 + n^(2^r)`.
- **Lemma 3.4.** Each term of `g S[v]T[w] g^(−1)` restricts `g ∘ (wy -> vy) ∘ g^(−1)`, with range in `g[v]` and domain
  in `g[w]`. `g` preserves order, so `g[v] < g[w]`.
- **Theorem 3.5.**
  - `U_<` is torsion and `F` is torsion-free, so the product is semidirect.
  - Locally finite by amenable is amenable, and a nontrivial `P` supplies an element of infinite order for
    Theorem S.
  - `F` is a quotient of `U_< ⋊ F`, which gives the "only if".
- **Example 3.6.**
  - (1) With `(p_1, p_2, p_3) = (0, 10, 11)`, `[A p_a u] ⊆ [A p_a] < [A p_b] ⊇ [A p_b u']`. This includes `A` empty,
    so the order-128 Toeplitz group lies in `U_<`.
  - (2) `x_0` maps `0 < 10 < 11` onto `00 < 01 < 1`, so it is in `F`. In `R^ω_≤` the pair `y = S[00]T[0]`,
    `z = S[0]T[00]` has `zy = e_0` and `yz = e_00`, so `XY = 1` and `YX = 1 − e_01`. The `R^ω_≥` case uses
    `S[1]T[11]` and `S[11]T[1]` in the corner `e_1`.
- **Corollary 3.7 and characteristic three.** The torsion of `U_< ⋊ P` lies in `U_<`. `−1` would need `1 in T_<`, but
  `T_<` is locally nilpotent. `(1 + n)^(3^r) = 1 + n^(3^r)` makes `U_<` a 3-group.

### 35.3 One-chart coefficients (Section 4). PASS

- **Fact 4.1.** `S/I` is finite over `F_2`, so `GL_#Q(S/I)` is finite.
- **Corollary 4.2.** `iota_(A_i)(x_ab(c)) = Phi_Q(1 + c E_(A_i p_a, A_i p_b))` for `c in S`. Item 3 of the right-child
  node supplies infinite order.
- **Lemma 4.3, recomputed.**
  - Conjugation by the permutation `pi` carries `u E u^(−1) < E_(q')` to `E' < E`.
  - `W^(−1) E' W = E` gives `xy = E`, and `W E W^(−1) = E'` gives `yx = E'`.
  - `x`, `y` lie in `E M_Q(S) E`, so the cross terms vanish, and `XY = 1`, `YX = 1 − (E − E')`.
  - **Ideal step.** `(1 − ab) a = 0 = b (1 − ab)`. So in `(1 − ab) b^k a^i b^(i') a^l (1 − ab)` a term survives only if
    `i = k` and `i' = l`, or `i < k` on the same diagonal. The minimal choice of `k` makes the second case have
    coefficient `0`.
  - Products of finite-dimensional algebras are directly finite.
- **Corollary 4.4.** The leftmost leaf of `Q != {empty}` is `0^k` with `k >= 1`, and `x_0` carries `[0^k]` onto
  `[0^(k+1)]`.
