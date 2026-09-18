---
rg: 2
id: cnd-ball-growth-return-probability-proof
kind: route
title: Cocycle expansion, a nonnegative spectral kernel, then Markov and Cauchy–Schwarz
target: cnd-ball-growth-bounds-return-probability-for-every-group
requires: []
---

Notation as in the target. "cnd" means: `psi` is real, `psi(g^{-1}) = psi(g)`, and
`sum_{g,h} a_g a_h psi(h^{-1} g) <= 0` whenever `sum_g a_g = 0`.

**Step 0. Cocycle (GNS).**
- *Space.* On `V = {a in R[G] : sum a_g = 0}` put `<a, a'> = -1/2 sum_{g,h} a_g a'_h psi(h^{-1} g)`.
  This is positive semidefinite. Quotient by the null space and complete to a real Hilbert space `H`.
- *Action.* Left translation `pi(k) delta_g = delta_{kg}` preserves `V` and the form, since
  `psi((kh)^{-1} kg) = psi(h^{-1} g)`. So it induces an orthogonal representation.
- *Cocycle.* `b(g) = [delta_g - delta_e]` satisfies `b(gh) = b(g) + pi(g) b(h)`.
- *Norm.* `||b(g)||^2 = -1/2 (0 - psi(g) - psi(g^{-1}) + 0) = psi(g)`.

**Step 1. Expansion.** Iterating the cocycle identity gives
`b(X_n) = sum_{i=1}^n pi(X_{i-1}) b(s_i)`. Hence `psi(X_n) = sum_i psi(s_i) + 2 sum_{i<j} T_{ij}` with
`T_{ij} = <pi(X_{i-1}) b(s_i), pi(X_{j-1}) b(s_j)> = <pi(s_i^{-1}) b(s_i), pi(s_{i+1} ... s_{j-1}) b(s_j)>`.

**Step 2. Cross terms.**
- *Rewriting.* The cocycle identity at `s^{-1} s = e` gives `pi(s^{-1}) b(s) = -b(s^{-1})`.
- *Operators.* Put `P = sum_s mu(s) pi(s)`. It is self-adjoint because `mu` is symmetric and `pi` is
  orthogonal, and `||P|| <= 1`. Put `beta = sum_s mu(s) b(s) = sum_s mu(s) b(s^{-1})`, using symmetry.
- *Expectation.* The `s_i` are independent, so `E T_{ij} = -<beta, P^{j-i-1} beta>`.
- *Counting.* For `0 <= k <= n-2` there are `n-1-k` pairs `i < j` with `j - i - 1 = k`. So
  `E psi(X_n) = n c - 2 <beta, Q_{n-2}(P) beta>`, where `Q_m(x) = sum_{k=0}^m (m+1-k) x^k`.

**Step 3. Positivity.**
- *Identity.* `Q_m(x) = sum_{j=0}^m (1 + x + ... + x^j)`.
- *Sign.* For `x in [-1, 1)`, each inner sum equals `(1 - x^{j+1})/(1 - x) >= 0`; at `x = 1` it is `j+1`.
  So `Q_m >= 0` on `sigma(P) ⊆ [-1, 1]`.
- *Conclusion.* The spectral theorem gives `<beta, Q_m(P) beta> >= 0`, hence `E psi(X_n) <= n c`.
  This proves item 1; for `n <= 1` it is immediate.

**Step 4. Return probability.**
- *Markov.* Put `R = 2cn`. Item 1 and Markov's inequality give `P(psi(X_n) > R) <= 1/2`, so
  `u_n(B_R) >= 1/2`.
- *Symmetry.* `mu` is symmetric, so `u_n(g^{-1}) = u_n(g)`, and
  `p_{2n} = sum_g u_n(g) u_n(g^{-1}) = sum_g u_n(g)^2`.
- *Cauchy–Schwarz.* If `|B_R| < inf`, then `sum_g u_n(g)^2 >= u_n(B_R)^2 / |B_R| >= 1/(4 |B_R|)`.
  This proves item 2.

**Step 5. Consequence and the l^2 equivalence.**
- *Consequence.* If `log |B_R| = o(R)`, then `p_{2n} >= exp(-o(n))`, so `limsup p_{2n}^{1/(2n)} = 1`.
  Kesten's theorem (H. Kesten, *Full Banach mean values on countable groups*, Math. Scand. 7 (1959))
  says that for a symmetric generating `mu` this forces `G` to be amenable.
- *The l^2 inequalities* are the two displayed in the target. The first is the tail bound
  `sum_{psi(g) <= R} e^{-2t psi(g)} >= |B_R| e^{-2tR}`. The second groups `g` by `floor(psi(g))`.
  If `log|B_R| = o(R)`, the series `sum_j |B_{j+1}| e^{-2tj}` converges for every `t > 0`.
