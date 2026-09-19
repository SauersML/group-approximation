# gq-referee-b: `leavitt-resolvent-k2-stability-holds` and its two inputs (citation and hypothesis lens)

Nodes and routes as landed at eecdc0a2f (lane gq-infinite-primes):
- `leavitt-resolvent-k2-stability-holds` (+ `-proof`);
- `leavitt-resolvent-frame-complex-is-highly-connected` (+ `-proof`);
- `leavitt-ge-rings-have-stable-k1-at-rank-three` (+ `-proof`).

Sources:
- Khanh, arXiv:2609.08428, TeX at `gq/src/on/2609.08428/khanh.tex`;
- Ara–Goodearl–Pardo, arXiv:math/0111066v1, PDF read;
- Weibel, *K-book*, Ch. III, PDF read.

**Verdict: PASS.** I checked the lane's five questions (a)–(e) at source.
- **(a), (b), (d)** hold as the lane claims, with one additional input for (a) that should be listed: the explicit
  vertex and edge stabilizers and `η(K) = K`.
- **(c)** is now pinned one level closer to the source, through AGP, who cite Menal–Moncasi for the GE property of
  every purely infinite simple ring. AGP's own Theorem 1.6 converts the lane's compression `yxz = 1` into "purely
  infinite simple".
- **(e)** Brown is not read, but it is not needed. Khanh's proof contains a direct path-groupoid verification of the
  presentation.
- Wording points W1–W4.

## (a) What Khanh's proof of `thm:raw-criterion` (l.430–495) uses

**Hypotheses.** The theorem has three: characteristic 2, `GL = E` in ranks `n−1` and `n−2`, and `j(N_(n−1)) = 1`,
together with simple connectivity. Each enters the proof at a definite point.

**The presentation of `G`** (l.442–462). This part uses exactly:
- transitivity on ordered `k`-frames for `k = 1, 2, 3` (l.442: "one orbit in each of dimensions zero, one, and two");
- the explicit stabilizers `J` of the vertex `b_1` and `K` of the ordered edge `(b_1, b_2)` (l.444–447);
- `τ = (12)` with `τ b_1 = b_2`, and `η(k) = τ k τ^(−1)`, which maps `K` to itself because `K` fixes both `b_1` and
  `b_2`;
- `h = (23) ∈ J`;
- the triangle computation "`ThT` has projection `(13)` and path `b_1 → b_2 → b_3`, whereas `hTh` has the same
  projection and path `b_1 → b_3`" (l.458);
- `h^2 = 1`, which gives `T^2 = 1` "from the displayed presentation" (l.460);
- simple connectivity, used only in "The homotopy sequence of `|X_n(B)| → Y → BG`" (l.462).

`GL_n` itself is used only through transitivity ("a basis of a permitted complement completes the frame", l.442) and
through the shape of `J` and `K`. So the lane's list is right, with one addition: the stabilizer descriptions (W4).

For `G = E_n(R_L)`, the lane supplies each item:
- transitivity: frame-complex node, item 4;
- `J ∩ E_n` and `K ∩ E_n`, with `H ∈ E_(n−1)` and `H ∈ E_(n−2)`: (K1) at ranks `n−1, n−2 ≥ 3`, so `n ≥ 5`, as fixed
  in the route;
- `P_12, P_23 ∈ E_n`: (K1) and `[−1] = 0`;
- simple connectivity: frame-complex node, item 3.

The unsigned permutation matrices keep `τ^2 = h^2 = 1` and the path computations unchanged. ✓

**The lift to `S`** (l.464–495). This part uses:
- `ℓ`, well defined by hypotheses 1 and 2;
- the row identity (eq:row-action), from the Steinberg relations alone;
- `ℓ_0`, from the null words on coordinates `3..n`, killed by hypothesis 2;
- the Weyl identity (eq:weyl-action), which is where characteristic 2 enters: "By additivity in characteristic two,
  `w_ij^2 = 1`";
- surjectivity from the generator list.

The route replaces the first two with "modulo the central `C = j(K_2(n−1))`" (padded centrality, l.498–508), and the
Weyl element with the exact `ω_12`. Both replacements are sound:
- Every relation of `Π` is checked in `S/C`. `T^2 = 1` is not a defining relation of `Π`, so `ψ(T)^2 ∈ C` is not even
  needed.
- The braid relation holds modulo `C` because the quotient of the two words is a word on coordinates `1, 2, 3` in
  `K_2(n)`. Viewed in the copy of `St_(n−1)` on coordinates `1..n−1`, it lies in that copy's `K_2(n−1)`, since
  `E_(n−1) ↪ E_n`. That copy's image is `C` by (Z). ✓

## (b) What Khanh's `prop:frame-cone` (l.360–391) uses

The proof uses:
- the comb `L_q` and the identities `LL^* = 1`, `L^*L = I` (`lem:leaf-coordinates`, l.264–284);
- `lem:word-multiplier` (l.338–358), applied once to the `a_i`;
- the sibling kernels `ker η^* = ⊕ s_l R` (eq:sibling-kernel, inside the proof of `lem:word-multiplier`);
- formal module algebra: the decomposition (eq:cone-decomposition), its explicit inverse, and the formal-size
  isomorphism (eq:complement-formal-coordinates);
- the fact that a right-module endomorphism of `R` is left multiplication.

The only ring-specific input is the multiplier lemma. Its proof uses `F_2`-normal forms, and the lane replaces it with
its own item 1. Leaf coordinates and sibling kernels hold in any ring with a Leavitt pair, as the lane says. ✓

The fan argument for simple connectivity (proof of `thm:steinberg-isomorphism`, l.539–541) uses `prop:frame-cone` for
vertices and edges only, which needs `r − 2 ≥ 2`. ✓

## (c) Menal–Moncasi GE, through Ara–Goodearl–Pardo

AGP, arXiv:math/0111066v1, read at source (pp. 5, 8). Khanh's bibliography entry is K-Theory 26 (2002).
- **Theorem 1.6, p. 5.** "Let `R` be a simple ring. Then `R` is purely infinite if and only if (a) `R` is not a
  division ring, and (b) For every nonzero element `a ∈ R`, there exist elements `x, y ∈ R` such that `xay = 1`."
- **Theorem 2.4, p. 8.** "If `R` is a purely infinite simple ring then `K_1(R) = U(R)^ab`." Its proof opens: "By
  [23, Remark after 2.3], `R` is a `GE`-ring".
  - This is the published "Theorem 2.3" that Khanh cites. The arXiv v1 numbers it 2.4.
  - [23] is the Menal–Moncasi reference, J. Pure Appl. Algebra 33 (1984), in Khanh's list.
- **No regularity assumption.** AGP's §1–2 definitions and statements are for arbitrary unital simple rings. The
  regularity in their title is not used in Theorems 1.6 and 2.4. This supports Khanh's "requires no regularity
  assumption".
- **Application to `R_L`.** `R_L` is simple, and not a division ring, since it has nontrivial idempotents `q_k`. The
  compression node gives `yxz = 1`. So `R_L` is purely infinite simple by AGP Theorem 1.6, and GE by AGP Theorem 2.4's
  citation of Menal–Moncasi. ✓
- Menal–Moncasi itself was not reached, since it is not on arXiv.
- A consistency check: AGP Theorem 2.4 also gives `K_1(R_L) = U(R_L)^ab`, which agrees with `K_1(R_L) = Z`.

## (d) Steinberg identities for `w_12(x)` and `h_12(x)`, arbitrary units

Weibel III, Example 5.10.1 (p. 43): `w_ij(r) = x_ij(r) x_ji(−r^(−1)) x_ij(r)` and `h_ij(r) = w_ij(r) w_ij(−1)`, "for
any unit `r` of `R`". These are the lane's definitions.

Weibel III, Exercise 5.8 (p. 46): "the following identities hold in `St(R)` (for `i`, `j` and `k` distinct)":
- (a) `w_ij(r) w_ij(−r) = 1`;
- (b) `w_ik(r) x_ij(s) w_ik(−r) = x_kj(−r^(−1) s)`;
- (c) `w_ij(r) x_ij(s) w_ij(−r) = x_ji(−r^(−1) s r^(−1))`;
- (d) `w_ij(r) x_ji(s) w_ij(−r) = x_ij(−r s r)`;
- (e) `w_ij(r) w_ji(r^(−1)) = 1`.

These are stated for an arbitrary ring, with the noncommutative order of factors, and use only three indices, so they
hold in `St_n`, `n ≥ 3`.

**Consequences.**
- From (b), and from (a)+(e), which give `w_12(r) = w_21(−r^(−1))`:
  - `w_12(r) x_1k(c) w_12(r)^(−1) = x_2k(−r^(−1) c)`;
  - `w_12(r) x_2k(c) w_12(r)^(−1) = x_1k(r c)`.
  These are the route's formulas.
- The column cases follow the same way.
- `h_12(r)` then acts on every generator exactly as `diag(r, r^(−1))`. I checked `x_1k`, `x_2k`, and, with (c) and
  (d), `x_12 ↦ x_12(rcr)`. So `d_1` acts exactly as `diag(−1, 1, …)`, and `ω_12 = w_12(1) d_1` acts exactly as
  `P_12`. ✓
- The sign computation: `a^2 = W^2 = 1` and `WaW = −a`, so `[a, W] = −1`. I checked it from the Leavitt relations. ✓

## (e) Brown's presentation theorem

Brown, J. Pure Appl. Algebra 32 (1984), is not on arXiv and was not read. Khanh does not depend on it: l.458–460 give
a self-contained verification. The fundamental group of the Borel construction is identified with pairs `(g, [p])`,
and completeness is checked by edge-path homotopies ("backtracking and passages across individual triangles"). That
argument is general, and uses only the items listed in (a). So the route may rest on Khanh's paragraph instead of on
Brown (W3).

## Warnings

- **W1.** Route, Step 1: "`j(b, H)` is `x_1(b) diag(1, H)`" has the factors in the wrong order.
  `x_1(b) diag(1, H) = [[1, bH], [0, H]]`, and `j(b, H) = diag(1, H) x_1(b)`, matching Khanh's `σ = ℓ(H) x_1(b)`.
  Membership in `G` is unaffected.
- **W2.** Cite GE as "AGP Thm 1.6 (purely infinite ⇔ compression) and AGP Thm 2.4 [2.3 in print], whose proof cites
  Menal–Moncasi, Remark after 2.3", and keep "Menal–Moncasi not read". Khanh's phrase "Theorem 2.3" refers to the
  published numbering.
- **W3.** Replace "Brown's theorem" in Step 1 with "Khanh's direct verification (l.458–460), following Brown". Brown
  remains unread.
- **W4.** Add to the list of used features: the explicit stabilizers `J`, `K` of `b_1` and `(b_1, b_2)` in `G`, and
  `η(K) = K`.
