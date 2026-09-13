
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

### 35.4 Lemma 6.1 (Section 6). CORRECTION to the hypothesis; PASS in the corrected form

**The literal statement is false.** Read literally, the hypothesis says that each positive root of the frames at `A`
and `A1` moves all its points strictly one way. Under that hypothesis the conclusion "all of them move the same way"
fails, and `b` preserves some such order.

- **Counterexample.** Identify `[A]` with `X` through `Ay -> y`. On `[A]`, `b` is `0y -> 0y`, `10y -> 100y`,
  `110y -> 11y`, `111y -> 101y`. Let `phi_2(0y) = 1 phi_2(y)` and `phi_2(1y) = 0y`, and put
  `Psi = (0y -> 0y, 10y -> 10y, 111y -> 110y, 110y -> 111 phi_2(y))`. Order `[A]` by `xi ≺ eta` iff
  `Psi(xi) <_lex Psi(eta)`, and order the rest of `X` lexicographically, with the block `[A]` in its place.
- **`b` preserves `≺`.** Recomputed: `Psi b Psi^(−1)` is `0 -> 0`, `10 -> 100`, `110 -> 101`, `1110 -> 110` and
  `1111 -> 111`. For the last two:
  - `phi_2^(−1)(0w) = 1w`, and `1110w -> 110 1w -> 111w -> 110w`;
  - `phi_2^(−1)(1w) = 0 phi_2^(−1)(w)`, and `1111w -> 110 0 phi_2^(−1)(w) -> 11 0 phi_2^(−1)(w) -> 111w`.

  The domain code `0 < 10 < 110 < 1110 < 1111` goes to `0 < 100 < 101 < 110 < 111`, so this is in `F`, and `b`
  preserves `≺`.
- **Directions.** The blocks are ordered `[A0] ≺ [A10] ≺ [A111] ≺ [A110]`. So:
  - at `A`, `S[A0]T[A10]`, `S[A10]T[A11]` and `S[A0]T[A11]` move down;
  - at `A1`, `S[A10]T[A110]` and `S[A10]T[A111]` move down, but `S[A110]T[A111]` moves up.

  Every root moves its points strictly one way, not all the same way, and `b` preserves the order.
- **Where the proof slips.** "Same direction" shows only that `S[A10]T[A110]` follows the roots at `A`. The root
  `S[A110]T[A111]` compares two subcylinders of `[A11]`, and no root at `A` constrains them.

**Corrected statement.** Consider total orders on `X` in which the positive roots of each frame all move points
strictly one common way. Then both frames move the same way, and no such order is preserved by `b`.
- The artifact's two steps prove this.
- "Same direction" transfers the direction of the frame at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
- "Not preserved" uses the downward roots `S[A10]T[A110]` and `S[A110]T[A111]`. They give `[A100] ≺ [A11] ≺ [A101]`,
  which is impossible because `[A101] ⊆ [A10] ≺ [A11]`.

**Consequences.**
- **Section 6, item 1.** "Lemma 6.1 rules out the mechanism of Theorem 3.5" stands. That mechanism needs all six roots
  in one `T_≺`, which is one common direction.
- **Contraction.** `b` sends `[A10 0^k]` onto `[A10 0^(k+1)]`. On `[A1]` it is three prefix replacements, so Section 2
  does not apply.
- **What the counterexample does not show.** It gives no amenability or soficity of `Gamma_b`, which stays open.
- **Wording to correct forward.** Two sentences use the literal wording, "no order preserved by `b` makes both frames'
  positive roots monotone":
  - the Scope of `lex-decreasing-units-with-order-preserving-letters-are-amenable` (line 38);
  - the w7-sub-multiletter entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (line 231).

  Both should say "monotone in one common direction". The plans artifact (line 426) already says "all move one way",
  which is correct. No claim statement depends on the literal version.

### 35.5 Model tests, displays, routes, subsumption and scope. PASS

- **Section 5, item by item.**
  - Free sofic model: Proposition 2.3 with Theorem S's `rho` gives `(3/8)^2` on the sofic `G wr S_2`.
  - Finite subgroups: the order-128 group lies in `UT_3(R) <= U_<`, as in 35.2.
  - Right-child items 2–4:
    - the four positive roots lie in `T_<`, since `A0 < A10 < A110 < A111`;
    - `x^A_12(s_0) x^A_21(1)` uses a negative root;
    - the frame entries of `iota_A(w_23)` include `s_0`, `s_1`, `t_0`, `t_1`, and `b` contracts `e_(A10)`.
  - Jacobson nodes: `binary-jacobson-el3-is-sofic` and the halves node read as in Sections 31–32 here, and property (T)
    with residual finiteness is no conflict.
  - Depth-monotone: Example 3.6(2) and Corollary 4.4.
  - Ternary target: line 29 records `theta = 1` for independent factors.
  - Toeplitz quarter: its group lies in `U_<`.
- **Claim displays.**
  - Split-cylinder: Statements 1–3 are Lemmas 2.1–2.2 and Proposition 2.3 as re-derived in 35.1. The Consequence is
    Corollary 2.4. The Scope is Section 2's, including characteristic three.
  - Lex claim: items 1–4 are Lemmas 3.1–3.4, Theorem 3.5 and Example 3.6(1). The Consequences are 3.6(2), 3.7 and
    characteristic three. The Scope sentence is corrected in 35.4.
- **Entries.**
  - The entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `da18a78a`) and the one on the
    ternary target summarize Sections 2–4 and the characteristic-three port accurately. The wording on line 231 is as
    in 35.4.
  - The plans record (blob `19de3bf9`, lines 412–426) is accurate.
- **Routes.**
  - `lex-decreasing-units-order-preserving-letters-amenability-proof` requires
    `sofic-subgroups-carry-independent-cylinder-defects`, which is ESTABLISHED. Its five steps are 35.2.
  - `split-cylinder-data-defect-firewall-proof` requires nothing, and Statements 1–3 are self-contained.
  - Advisory: the claim's Consequence uses Theorem S and the defect gap, both ESTABLISHED, and the route may list them.
- **Subsumption scan at `0bb651f36d`.** `tau_AB`, `wr S_k`, `U_<`, "lexicographically decreasing" and "Borel group" hit
  28 research files. Outside this lane's files the hits are other notation:
  - the sign involutions `[tau_(A_i)]` of the characteristic-three descent;
  - barycenters;
  - Steinberg coordinates;
  - `H wr S_k` for finite-index overgroups;
  - function-field Borel groups.

  The four-transvection escape artifact consumes `U_< ⋊ P` as a firewall. The right-child node (item 4) and Section 4
  of the locally-finite-conjugation artifact prove finiteness for four positive roots through a potential, and
  Lemma 3.2 generalizes that, which `distinct_from` records. No duplicate.
- **Scope.** Each firewall is conditional: a deficit from these relations would imply the gate, or would imply that
  `F` is nonamenable, or it contradicts Theorem S. None of them forces a rank model or `theta` to be trivial. The next
  live systems, `Gamma_b`, `U_< ⋊ F` and `EL_3(J)`, stay OPEN.
