---
rg: 2
id: fibonacci-words-model-balls-proof
kind: route
title: Fibonacci words are primitive and their squares and near-cubes occur in X; read the r-ball through windows of radius 2r for products and r for differences
target: fibonacci-words-model-balls-of-fibonacci-kazhdan-group
requires: []
artifacts:
  - research/artifacts/sk-open-3-fibonacci-models-2026-09-13-part1.md
---

Direct proof. The full text is in the artifact §1–2. Recalled input: Morse–Hedlund. If a bi-infinite sequence has at
most L words of length L for some L, then some `L' ≤ L` has unique right extensions, and the sequence has a period at
most L'.

**Item 1.**
- Counting letters: `|f_k|_b = |f_{k-2}|`, and `gcd(|f_k|, |f_{k-2}|) = gcd(|f_{k-1}|, |f_{k-2}|) = 1`. So `f_k` is not a
  proper power, and `z^∞` has least period N. By Morse–Hedlund it has `≥ L+1` words of length `L < N`.
- `f_{k+3} = f_{k+1} f_k f_k f_{k-1}` contains `zz`. So every word of `z^∞` of length `≤ N+1` occurs in X.
- `|L_L(X)| = L+1`, since X is Sturmian. So the words of length L coincide.

**Item 2.**
- By induction from `f_2 f_1 = aba`, `f_1 f_2 = aab`: `f_j f_{j-1}` and `f_{j-1} f_j` differ exactly in their last two
  letters.
- `f_{k+4} = f_{k+1} f_k f_k f_{k-1} f_k f_{k-1} f_k` contains `zz f_{k-1} f_{k-1} f_{k-2}`.
- After `zz`, the sequence `z^∞` continues with `f_{k-1} f_{k-2} f_{k-1} …`, which agrees with
  `f_{k-1} f_{k-1} f_{k-2}` on its first `N + |f_{k-1}| - 2` letters.
- So the prefix of `z^∞` of length `3N + |f_{k-1}| - 2` occurs in X. It contains every window of length
  `M ≤ 2N + |f_{k-1}| - 1 = |f_{k+2}| - 1` starting in `[0, N)`.
- Attainment is computed.

**Item 3.**
- `u^a χ_{[x_0=a]} u^{-a} = χ_{[x_{-a}=a]}`. So a product of m letters from `{1, u^{±1}, χ_{[x_0=a]}}` is
  `(∏ χ_{[x_{-a_t}=a]}) u^{a_m}` with `|a_t| ≤ m`.
- Entries of `B_r` involve windows in `[-r, r]` and exponents `≤ r`. Entries of `B_r B_r` involve windows in
  `[-2r, 2r]`.
- For f depending on `[-2r, 2r]`, put `D_z(f)_{nn} = f(x)` for any x ∈ X agreeing with `z^∞` on `[n-2r, n+2r]`. Such x
  exists by item 2, since `4r+1 ≤ 2N-3 ≤ |f_{k+2}| - 1`.
- D_z is a ring homomorphism on these functions, and `P^i D_z(g) P^{-i} = D_z(g∘T^{-i})` inside the window. So
  `φ_z(gh) = φ_z(g)φ_z(h)` on `B_r × B_r`, and `h = g^{-1}` gives invertibility.
- If `g ≠ h`, some entry `Σ f_j u^j ≠ 0` of `g - h` has `|j| ≤ r` and `f_j` depending on `[-r, r]`.
  - Since `N ≥ 2r+1`, the `D_z(f_j) P^j` have disjoint supports.
  - A nonzero `f_j` is 1 on the cylinder of some `v ∈ L_{2r+1}(X)`, and v occurs in `z^∞` by item 1 (`2r+1 ≤ N-1`).
  - So `φ_z(g) ≠ φ_z(h)`.
- Over F_2, `GL = SL`.

**Item 4.** Use item 1 for containment: `4r+1 ≤ N+1`. ∎

**Model test.**
- The trivial model: the periodic subshift of `(ab)^∞` has `|L_L| = 2`, so item 1 fails for `L ≥ 2`.
- The real object: X_Fib satisfies every hypothesis, and the exact-ball computation (artifact §4) agrees with item 3.
