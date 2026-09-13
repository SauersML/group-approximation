---
rg: 2
id: brin-thompson-exponent-cocycle-proof
kind: route
title: The vector exponent cocycle of nV has a conjugation-invariant, homogeneous periodic spectrum, so a proper-power relation kills it; trivial sections turn zero exponent into local identity, and table lengths bound the Birkhoff sums
target: bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
requires: []
---

Notation is as in the target. `|·|` on `Z^n` or `Q^n` is the sup norm.

**Step 0 (cocycle).**
- For `x ∈ C^n`, choose a table brick `Π C(u_j) ∋ x` of `g`, mapped to
  `Π C(v_j)`, and set `δ_g(x) = (|v_j| - |u_j|)_j`.
- **Well defined.** Splitting coordinate `j` of a table brick by one digit `a`
  gives the pair `C(u_j a) → C(v_j a)`, with the same difference. Any two tables
  have a common refinement obtained by such splittings, so they give the same
  `δ_g`. It is locally constant, and `|δ_g| ≤ L(g)`.
- **Cocycle.** Refine a table of `h` so that each domain brick `B ∋ x` is mapped
  into a single table brick of `g`, by appending digits to the domain and range
  words together. Then `gh` acts on `B` by prefix replacement, and the length
  differences add: `δ_{gh}(x) = δ_g(hx) + δ_h(x)`. With `h = g^-1` this gives
  `δ_{g^-1}(gx) = -δ_g(x)`.

**Step 1 (periodic spectrum).**
- For `x` of least period `p` under `g`, set `ρ_g(x) = δ_{g^p}(x)/p ∈ Q^n`. Let
  `R(g)` be the set of these values. `|ρ_g(x)| ≤ L(g)`, since `δ_{g^p}(x)` is a
  sum of `p` values of `δ_g`.
- **Conjugation.** `fx` has least period `p` under `fgf^-1`, and
  `δ_{f g^p f^-1}(fx) = δ_f(g^p x) + δ_{g^p}(x) + δ_{f^-1}(fx) = δ_{g^p}(x)`,
  because `g^p x = x` and `δ_f(x) + δ_{f^-1}(fx) = δ_{id}(x) = 0`. So
  `R(fgf^-1) = R(g)`.
- **Powers.** Let `m ≠ 0`. The `g^m`-periodic points are exactly the
  `g`-periodic points. If `x` has least `g`-period `p`, its least `g^m`-period is
  `p' = p/gcd(p,m)`. Then
  `δ_{(g^m)^{p'}}(x) = δ_{g^{mp'}}(x) = (mp'/p) δ_{g^p}(x)`, so
  `ρ_{g^m}(x) = m ρ_g(x)`. So `R(g^m) = m R(g)`.
- **Conclusion.** `k R(g) = R(g^k) = R(f g^k f^-1) = R(g^l) = l R(g)`.
  Say `|k| < |l|`, and let `s = sup{|ρ| : ρ ∈ R(g)} ≤ L(g)`.
  - If `s > 0`, pick `ρ ∈ R(g)` with `|ρ| > s|k|/|l|`.
  - Then `lρ ∈ l R(g) = k R(g)`, so `lρ = kρ'` with `ρ' ∈ R(g)`, and
    `|ρ'| = |l||ρ|/|k| > s`. That is a contradiction.
  - So `R(g) ⊆ {0}`. If `|k| > |l|`, exchange the roles of `k` and `l`.
- This proves item 1.

**Step 2 (local identity).**
- Let `g^p x = x` with `δ_{g^p}(x) = 0`. Take a table brick `Π C(u_j) ∋ x` of
  `g^p`, mapped to `Π C(v_j)`, with `|v_j| = |u_j|`.
- Write `x = (u_j w_j)_j`. Then `g^p x = (v_j w_j)_j = x`, so `v_j` is the prefix
  of `x_j` of length `|u_j|`. That prefix is `u_j`, so `v_j = u_j`.
- Hence `g^p` is the identity on `Π C(u_j)`, and every point of that brick is
  periodic. This proves item 2.

**Step 3 (aperiodic core).**
- **If `Per(g) = C^n`.** By Step 2, each point lies in a brick on which some
  `g^{p}` is the identity. By compactness, finitely many bricks with exponents
  `p_1, …, p_r` cover `C^n`, and `g^P = id` for `P = lcm(p_i)`.
- **Conversely.** Finite order makes every point periodic.
- **The core.** `Per(g)` is open and `g`-invariant, so `K(g)` is closed and
  invariant, contains no periodic point by definition, and is nonempty exactly
  when `g` has infinite order. This proves item 3.

**Step 4 (logarithmic exponents, `k = ±1`).**
- **Normalization.** If `k = -1`, then `f g f^-1 = g^{-l}`. So assume `k = 1`,
  `|l| ≥ 2`.
- **Table lengths.**
  - Composing tables as in Step 0 appends at most `L(g)` digits to the words of
    `h`. So `L(gh) ≤ L(g) + L(h)`.
  - Inverting swaps domain and range, so `L(g^-1) = L(g)`.
  - Hence `L(g^{l^j}) = L(f^j g f^-j) ≤ 2j L(f) + L(g)`.
- **Digits.**
  - Every integer `N` has an expansion `N = Σ_{j=0}^{J} d_j l^j` with
    `0 ≤ d_j < |l|`. Use the division algorithm `N = l q + d`, `0 ≤ d < |l|`.
  - Then `|q| ≤ (|N| + |l|)/|l| ≤ |N|/2 + 1`. So the absolute values fall below
    `3` after at most `log_2 |N| + 1` steps. From there only boundedly many steps
    remain (a finite check for each `l`). Hence the process terminates with
    `J ≤ log_2 |N| + C_l`. This also works for negative `l`.
- **Bound.**
  - `g^N = Π_j (g^{l^j})^{d_j}`, so
    `L(g^N) ≤ Σ_{j ≤ J} d_j (2jL(f) + L(g)) ≤ |l| (J+1) (2J L(f) + L(g))`.
  - With `|δ_{g^N}| ≤ L(g^N)` this is `O((1 + log|N|)^2)`, uniformly in `x`.
- This proves item 4. ∎

**Remark.** Item 2 is where the triviality of sections is used. In almost
automorphism groups `g^p` could fix `x` with exponent `0` and act by a nontrivial
tree automorphism on the cone, and there the corresponding conclusion is
equicontinuity instead.
