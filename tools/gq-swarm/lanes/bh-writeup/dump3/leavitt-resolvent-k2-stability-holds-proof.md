---
rg: 2
id: leavitt-resolvent-k2-stability-holds-proof
kind: route
title: Run Khanh's comparison for E_n(R_L) acting on its highly connected frame complex, modulo the central image of K_2(n-1), with Weyl lifts supported on three coordinates
target: leavitt-resolvent-k2-stability-holds
requires:
  - leavitt-resolvent-frame-complex-is-highly-connected
  - leavitt-ge-rings-have-stable-k1-at-rank-three
  - leavitt-surjective-k2-stability-implies-injective
  - leavitt-refinement-identifies-unstable-k2-levels
  - leavitt-resolvent-stable-k2-class-is-computable
  - st-n-leavitt-resolvent-word-problem-reduces-to-k2
---

Fix `n >= 5`. Write `S = St_n(R_L)`, `G = E_n(R_L)`, `φ : S -> G`, and let `j` be stabilization.

**Step 0: inputs.**
- **(K1)** `GL_m(R_L)/E_m(R_L) -> K_1(R_L) = Z` is injective for `m >= 3` (`leavitt-ge-rings-have-stable-k1-at-rank-three`).
  So `diag(1, H) in E_(m+1)` implies `H in E_m` for `m >= 3`. Also `diag(-1, 1, ..., 1) in E_m` for `m >= 3`, since
  `[-1] = 0`: rational scalars die in `K_1(R_L)`.
- **(X)** `X = X_n(R_L)` is simply connected, and `G` acts transitively on ordered frames of size `1, 2, 3`
  (`leavitt-resolvent-frame-complex-is-highly-connected`, since `3 <= n - 1`).
- **(Z)** Padded centrality (Khanh, Lemma `lem:padded-centrality`, any unital ring): `j(K_2(n-1))` is central in `S`.
  Put `C = j(K_2(n-1))`. The image of `K_2(n-1)` on any `n - 1` of the coordinates is conjugate to `C` by a Weyl word,
  so it equals `C`, because `C` is central. The image of `K_2(n-2)` on any `n - 2` coordinates lies in `C`.
- An element of `j(St_(n-1))` that lies in `K_2(n)` lies in `C`, since `E_(n-1) -> E_n` is injective.
  The same holds for the copy of `St_(n-1)` on any `n - 1` coordinates.

**Step 1: the presentation of `G`.**
- Let `P_12` and `P_23` be the permutation matrices. `P_12 = τ̃ · diag(-1, 1, ...)` with `τ̃` the signed transposition,
  so `P_12 in G` by (K1). Likewise `P_23 in G`.
- The stabilizer of the vertex `b_1` is `J = {j(b, H) = [[1, b], [0, H]] in G}`. Here `j(b, H)` is `diag(1, H) x_1(b)`, matching `σ = ℓ(H) x_1(b)` (gq-referee-b, W1), so
  `j(b, H) in G` if and only if `diag(1, H) in G`, which by (K1) means `H in E_(n-1)`.
- The stabilizer of the ordered edge `(b_1, b_2)` is `K = {k(a, b, H)}`, with `H in E_(n-2)` by (K1), since `n - 2 >= 3`.
- By (X), Khanh's Borel-construction argument presents
  `G = <J, T | T k T^-1 = η(k) (k in K), T h T = h T h>`, with `T = P_12`, `h = P_23` and `η = conjugation by P_12`.
  Khanh verifies the presentation directly through the path groupoid (khanh.tex l. 458--460), so Brown is not needed
  (gq-referee-b, W3). The derivation uses only:
  - transitivity in dimensions `0, 1, 2`, and simple connectivity (used only at l. 462);
  - `T b_1 = b_2`, `h in J` and `h^2 = 1`;
  - the explicit stabilizers `J` of `b_1` and `K` of `(b_1, b_2)`, with `η(K) = K` (gq-referee-b, W4).
  `T^2 = 1` is derived from these, not imposed, so `ψ(T)^2 in C` is not needed; it holds anyway.

**Step 2: exact Weyl lifts on two coordinates.**
- **Signs.** Let `a = ee* - ff*` and `W = ef* + fe*`, with `(e, f) = (s_1, s_2)`. Then `a² = W² = 1` and `W a W = -a`, so
  `[a, W] = a W a W = -1`.
- For units `x`, put `h_12(x) = w_12(x) w_12(-1)`, which lifts `diag(x, x^-1)`, with `w_12(x) = x_12(x) x_21(-x^-1) x_12(x)`.
  These act on generators exactly by conjugation with their diagonal matrices: `w_12(x) x_1k(c) w_12(x)^-1 = x_2k(-x^-1 c)`
  and `w_12(x) x_2k(c) w_12(x)^-1 = x_1k(xc)` for `k >= 3`, and similarly for columns. These are the standard Steinberg
  identities.
- So `d_1 = h_12(a) h_12(W) h_12((Wa)^-1)` lifts `diag([a, W], 1, ...) = diag(-1, 1, ...)`. It acts exactly: it negates
  the generators with exactly one index equal to `1`, and fixes the rest. This follows from Khanh's identity
  `diag([a,b], 1) = diag(a, a^-1) diag(b, b^-1) diag(a^-1 b^-1, ba)`.
- `ω_12 = w_12(1) d_1` lifts `P_12` and conjugates every `X_ij(c)` to `X_(τ(i) τ(j))(c)`, `τ = (12)`, exactly. It is a word
  in the generators `X_12, X_21`. Define `ω_23` the same way on coordinates `2, 3`.

**Step 3: the section modulo `C`.**
- Following Khanh, define `ℓ : E_(n-1) -> S/C` on coordinates `2, ..., n` by evaluating elementary words. Two words
  differ by an element of `K_2(n-1)` placed on those coordinates, which lies in `C` by (Z).
- Define `ℓ_0` on coordinates `3, ..., n` in the same way. Put `σ(j(b, H)) = ℓ(H) x_1(b)` and
  `σ(k(a, b, H)) = ℓ_0(H) x_2(b) x_1(a)`.
- The row identity `ℓ(H) x_1(b) ℓ(H)^-1 = x_1(b H^-1)` holds exactly for elementary words (Khanh). So `σ` is a
  homomorphism on `J` into `S/C`.
- Put `ψ(T) = ω_12 C` and `ψ(h) = ω_23 C`. Since `ω_23` is a word on coordinates `2, 3`, it equals `σ(h)` modulo `C`.
- **Edge relation.** `ω_12` fixes the generators on coordinates `>= 3` and swaps `x_1(·)` with `x_2(·)` exactly. So
  `ω_12 σ(k) ω_12^-1 = σ(η(k))`.
- **Triangle relation.** Both `ω_12 ω_23 ω_12` and `ω_23 ω_12 ω_23` are words on coordinates `1, 2, 3`, and they lift the
  same matrix `P_13`. Their quotient lies in `K_2(n) ∩ (copy of St_3)`, which is in `C` by (Z), since `3 <= n - 1`.
- **`T^2`.** Similarly `ω_12^2` is a word on coordinates `1, 2` in `K_2(n)`, so it lies in `C`.
- So `ψ` extends to a homomorphism `Π -> S/C` with `φ ψ = p`. It is surjective: its image contains `X_ij` for
  `i, j >= 2`, and `X_1j`, and the `X_i1` are conjugates by `ω_12` (Khanh's last paragraph). `p` is an isomorphism, so
  `S/C -> G` is an isomorphism, and `K_2(n) = C = j(K_2(n-1))`.

**Items 1--3.**
- Step 3 gives item 1 with `m = n - 1 >= 4`.
- `leavitt-surjective-k2-stability-implies-injective`, item 2, then gives `U_m = 1` for every `m >= 4`.
  `leavitt-refinement-identifies-unstable-k2-levels`, item 2, gives `U_3 ≅ U_4 = 1`. So `K_2(N) ≅ K_2(R_L)` for all `N >= 3`.
- For centrality: `K_2(m+1) = j(K_2(m))` is central in `St_(m+1)` for `m >= 4`, by (Z). For `N = 3, 4`, transport through
  the refinement isomorphisms `D`, which carry centres to centres and `K_2` to `K_2`.

**Item 4.** This is item 2 of the present node, with items 2--3 of
`st-n-leavitt-resolvent-word-problem-reduces-to-k2` and `leavitt-resolvent-stable-k2-class-is-computable`, item 3. For
`N = 3`, use `St_3(R_L) ≅ St_4(R_L)` with computable `D` and `D^-1`.
