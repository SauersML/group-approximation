---
rg: 2
id: thompson-v-sym-rep-rank-models-local-embedding-proof
kind: route
title: 3-cycle commutators force exactness, and exact local embeddings of V do not exist
target: thompson-v-rank-models-through-displacing-sym-reps-are-trivial
requires:
  - thompson-v-finitely-presented-infinite-simple
---

**Bounded degree.** If `m_k = m` for ω-most `k`, then `phi(g) = lim_omega phi_k(g)` lies in the finite set
`S_m`. So `sigma(V)` lies in `{[pi_k(s)]_k : s in S_m}`, which has at most `m!` elements. A finite
quotient of the infinite simple group `V` is trivial. From now on assume `m_k >= 8` for ω-most `k`.

**Lemma 1 (two commutators reach a 3-cycle).** Let `z != 1` in `S_m` with `m >= 8`.
- Pick `a` with `z(a) != a`, and `c, d` distinct from `a` and `z(a)`. Put `u = (a c d)`.
- Then `z u z^(-1) = (z(a) z(c) z(d))` has a different support from `u`, since `z(a)` is outside
  `{a, c, d}`. So `y = [z, u]` is nontrivial, and its support has at most `6` points.
- Pick `p` in `supp(y)` and `q, r` outside it. Then `[y, (p q r)] = (y(p) q r)(p r q) = (p y(p) q)` is a
  3-cycle.

**Lemma 2.** In any representation `pi`, `rk(pi([g,h]) - 1) <= 2 rk(pi(g) - 1)`, because
`pi([g,h]) - 1 = ((pi(g) - 1) - (pi(h g h^(-1)) - 1)) pi(h g^(-1) h^(-1))`. With Lemma 1,
`rk(pi(z) - 1) >= rk(pi(t) - 1)/4` for every `z != 1`.

**Exactness.** Fix `g, h in V` and put `z_k = phi_k(g) phi_k(h) phi_k(gh)^(-1)` in `S_(m_k)`. Then
`pi_k(z_k) - 1 = (sigma_k(g) sigma_k(h) - sigma_k(gh)) sigma_k(gh)^(-1)` has rank `o(n_k)` along `omega`.
- If `z_k != 1`, Lemma 2 bounds this rank below by `d_k n_k / 4`.
- So `z_k = 1` for ω-most `k`.

**No model survives.** Suppose `sigma` is nontrivial.
- By simplicity `sigma` is injective. For `g != 1` there is `c_g > 0` with `rk(sigma_k(g) - 1) >= c_g n_k`
  for ω-most `k`, so `phi_k(g) != 1`.
- Take a finite presentation `<s_1, ..., s_r | R>` of `V` with `s_1 != 1`. Let `B` be a finite set
  containing `1`, the `s_i^(±1)`, and every prefix of every relator.
- For ω-most `k`, `phi_k` is exactly multiplicative on the finitely many pairs `(w, s_i^(±1))` with `w`
  and `w s_i^(±1)` in `B`. Taking `w = 1` and `w = s_i` gives `phi_k(1) = 1` and
  `phi_k(s_i^(-1)) = phi_k(s_i)^(-1)`. By induction along prefixes, the `phi_k(s_i)` satisfy `R` and
  define a homomorphism `psi : V -> S_(m_k)` with `psi(s_1) = phi_k(s_1) != 1`.
- `ker psi` is a proper normal subgroup, so it is trivial and `V` embeds in `S_(m_k)`. That is impossible
  since `V` is infinite. QED
