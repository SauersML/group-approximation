# Referee report (gq-referee-c): bffhz-closures-cannot-create-gl-n-q (and gl-n-q-fixes-a-vertex-in-free-splittings)

- **Nodes:**
  - `research/bffhz-closures-cannot-create-gl-n-q.md` and its `-proof` route;
  - its only input, `research/gl-n-q-fixes-a-vertex-in-free-splittings.md` and its `-proof`.
  - All landed e3c8c2d0c by lane `gq-typeA-bffhz`.
- **Lens:** independent re-derivation and calibration.
- **Verdict: PASS**, with four wording fixes (§3). None of them affects the established statements.

## 1. The fixed-vertex lemma (FV)

- **Step 1, divisible elements are elliptic.** A hyperbolic `g` has integer `ℓ(g) >= 1` and `ℓ(r^k) = kℓ(r)`.
  So `g` with roots of infinitely many orders cannot be hyperbolic. ✓
- **Step 2.** With trivial edge stabilizers, a nontrivial elliptic element fixes exactly one vertex. Its fixed
  set is a subtree, and a subtree with two vertices contains an edge. ✓
- **Step 3.** In a divisible locally cyclic `D`, any two nontrivial elements are powers of one nontrivial `w`.
  So they share `w`'s unique fixed vertex. ✓
- **Step 4.** Normalizers permute the fixed sets, so they fix `x_D`. ✓
- **The cases:**
  - `Aff(Q)`: via its normal `Q`. ✓
  - `U_3(Q)`: via its centre `≅ (Q,+)`. ✓
  - `GL_n(Q)` and `SL_n(Q)`: the torus fixes every root-group vertex `x_ij`. A nontrivial torus element in
    `SL_n` (`diag(2,1/2,1,…)`) forces all `x_ij` to coincide. Root groups generate `SL_n(Q)`, and together with
    the torus they generate `GL_n(Q)`. ✓
- **Subdivision remark.** Correct.

## 2. The closure statements

- **Item 1.** This is FV on the Bass–Serre tree of `A * B`. ✓
- **Item 2.**
  - `L = ⋃_k t^(-k) J t^k` is the kernel of the exponent map, by the normal form `t^(-a) j t^b`.
  - `t^(-k) j t^k ↦ β^(-k)(j)` is well defined and injective into `M * F_m`. This is exactly where
    `β ∈ Aut(M * F_m)` is used.
  - `H'` lies in `L`: `H'` is a derived group, and `(Q,+)` is divisible.
  - FV on the tree of `M * F_m` then puts the image of `H'` in a conjugate of `M`. ✓
  - The derived groups are right: `GL_n(Q)' = SL_n(Q)`, `SL_n(Q)` is perfect, `Aff(Q)' = Q`, and `U_3(Q)'` is the
    centre.
- **Item 3.**
  - `Aut_M` means automorphisms restricting to the identity on `M`. I checked this against BFFHZ,
    arXiv:2503.21882 §1, "a G-homomorphism is a group homomorphism φ: H → H′ such that the restriction φ|_G is
    the identity". The proof needs this reading.
  - `Aut(F_m)` is residually finite (Baumslag 1963), so divisible elements map to 1. Root elements are
    divisible, so `SL_n(Q) ≤ K_M`. `U_3(Q)` is a divisible nilpotent group.
  - `N = *_(w ∈ F_m) wMw^(-1)`: its quotient graph by `N` is the Cayley tree of `F_m`, so there is no free
    factor. `N` has trivial centre. Restriction to `N` is injective on `K_M`, and it acts on each free factor by
    `N`-conjugation. ✓
- **Survey citation.** "V contains no (Q,+)" is Higman, survey Theorem 4.4. The counter is shared, and 4.4 is
  `thm:NoSL3ZInV`. ✓

## 3. Wording fixes (requested; none changes a truth value)

- **(a) Item 2, statement.** "`H'` lies in a conjugate of `M`" is literally meaningless when `M ⊄ J *_β`.
  Write instead: "the image of `H'` under the embedding `L ↪ M * F_m` lies in a conjugate of `M`; in
  particular `M` contains a copy of `H'`."
- **(b) Item 3 and the proof.** The right translations `x_i ↦ x_i g` satisfy `α_g ∘ α_h = α_(gh)` under the usual
  composition. So they give `M`, not `M^op`. This is harmless, since `M ≅ M^op`.
- **(c) "What survives", outer extensions.**
  - In the scalar case, the image of `SL_n(Q)` in `Out(S)` is `SL_n(Q)` modulo `SL_n(Q) ∩ Z'`. For even `n`,
    that is `SL_n(Q)` when `-I ∉ Z'`. So the image may be `SL_n(Q)`, not `PSL_n(Q)`.
  - Write "`SL_n(Q)` or `PSL_n(Q)`".
  - The dichotomy itself is correct: a normal subgroup of `GL_n(Q)` either contains `SL_n(Q)` or is central.
- **(d) Attempts.** "For `m = 1`, `K_M = {x ↦ gxh}`" is stated without proof or citation. It needs `M` freely
  indecomposable and a relative Kurosh argument. It is plausible, and it sits in Attempts, but mark it
  "unproved" or cite it.

## 4. Calibration

- **BS(1,2).** `Z[1/2] ≤ BS(1,2)` fixes only an end, and the node's Scope section says so. Item 2 escapes this
  exactly through the hypothesis that `β` extends to an automorphism of `M * F_m`. Then `L` embeds in the free
  product, and FV applies. Without it, `L` need not embed, as in `BS(1,2)`. The hypothesis is used where it
  must be.
- **O1.** The item 3 argument is the O1 mechanism (a residually finite quotient kills divisibility), applied to
  `Aut(F_m)`. ✓
