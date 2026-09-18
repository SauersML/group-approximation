---
rg: 2
id: solvable-ancilla-realizations-of-binary-automata-affine-proof
kind: route
title: Cosets of normal subgroups are congruences; a non-sitewise rule drags every ancilla pair into the first crossing subgroup, and an abelian crossing factor turns data flips into configuration-independent translations
target: solvable-ancilla-realizations-of-binary-automata-are-affine
requires: []
---

**Conventions.**
- `G`, `tau`, `B`, `Q`, `psi`, `T`, `w` and `m_1, ..., m_k` are as in the claim, and `T o psi = psi o (tau x id_B)`.
- For `q in Q` write `psi^(-1)(q) = (a(q), b(q))`.
- `Delta_A = {(q, q') : a(q) = a(q')}` and `theta_B = {(q, q') : b(q) = b(q')}`.
- For `N` normal in `Q`, `theta_N` is the relation "same `N`-coset".
- Configurations `z = psi(x, y)` have `x in {0,1}^G` and `y in B^G`. So `T(z)(g) = psi(tau(x)(g), y(g))`.
- `tau` is **sitewise** if `tau(x)(g)` depends only on `x(g)`.

**Lemma 1 (congruences).** If `N` is normal in `Q` and `u in Q * F_k`, then `q_j theta_N q'_j` for all `j`
implies `u(q) theta_N u(q')`.

*Proof.* The quotient map `Q -> Q/N` is a homomorphism. It commutes with evaluating words with constants. `QED`

**Lemma 2 (crossing).** Let `N` be normal in `Q` with `theta_N not subset Delta_A`, and let `tau` be non-sitewise.
Then `theta_B subset theta_N`: for every `c in B`, `psi(0, c)` and `psi(1, c)` lie in one `N`-coset.

*Proof.*
1. Since `tau` is non-sitewise and `G`-equivariant, there are `m != 1` in `G` and configurations `x`, `x'` that
   differ only at `m`, with `tau(x)(1) != tau(x')(1)`.
2. Choose `q theta_N q'` with `a(q) != a(q')`. Swapping `q` and `q'` if necessary, assume `a(q) = x(m)` and
   `a(q') = x'(m)`.
3. Fix `c in B`. Let `y`, `y'` agree off `m`, with `y(1) = c`, `psi(x(m), y(m)) = q` and `psi(x'(m), y'(m)) = q'`.
4. Then `z = psi(x, y)` and `z' = psi(x', y')` agree off `m`, and `z(m) theta_N z'(m)`.
5. `T(z)(1)` is `w` evaluated at finitely many sites. By Lemma 1, `T(z)(1) theta_N T(z')(1)`.
6. These values are `psi(tau(x)(1), c)` and `psi(tau(x')(1), c)`. They have different data bits and the same
   ancilla `c`, so they are `psi(0, c)` and `psi(1, c)` in some order.
7. `c` was arbitrary. `QED`

**Lemma 3 (affine fibres).**
- Let `M subset N` be normal subgroups with `N/M` abelian. Put `Qbar = Q/M` and `Nbar = N/M`, and write `Nbar`
  additively.
- For `s in Qbar` let `kappa_s` be the automorphism `n -> s n s^(-1)` of `Nbar`.
- Fix `s_1, ..., s_k in Qbar`.

Then for every `u in Qbar * F_k` there are an endomorphism `L_j` of `Nbar` for each `j`, and `U in Qbar`, both
depending only on `u` and the `s_j`, such that for all `n_1, ..., n_k in Nbar`:

    u(n_1 s_1, ..., n_k s_k) = (sum_j L_j(n_j)) U.

Each `L_j` is a signed sum of automorphisms `kappa_s`.

*Proof.* Induction on the length of `u`.
- **Constant letter `c`.** Take all `L_j = 0` and `U = c`.
- **Letter `x_j`.** Take `L_j = id` and `U = s_j`.
- **Letter `x_j^(-1)`.** `(n_j s_j)^(-1) = s_j^(-1) n_j^(-1) = kappa_(s_j^(-1))(-n_j) s_j^(-1)`.
- **Product `u = u' u''`.** Write `u' = alpha U'` and `u'' = beta U''` with `alpha, beta in Nbar`. Then
  `alpha U' beta U'' = (alpha + kappa_(U')(beta)) U' U''`, because `Nbar` is normal. `U'` depends only on the
  `s_j`, so the new coefficients are `L'_j + kappa_(U') L''_j`. `QED`

**Theorem A.** Let `M subset N` be normal subgroups of `Q` with:
- `theta_M subset Delta_A`;
- `theta_N not subset Delta_A`;
- `N/M` abelian.

If `T` realizes `tau`, then `tau` is affine over `F_2`.

*Proof.*
1. **Sitewise case.** If `tau` is sitewise, its local rule is a function `{0,1} -> {0,1}`, and every such
   function is affine. Assume from now on that `tau` is not sitewise.
2. **Ancilla determines the `N`-coset.** By Lemma 2, `psi(x, y)(h)` modulo `N` depends only on `y(h)`.
   - Work in `Qbar = Q/M` and fix a set-theoretic section `sigma` of `Qbar -> Q/N`.
   - For `c in B` put `s(c) = sigma(psi(0, c) mod N)`. By Lemma 2 this equals `sigma(psi(1, c) mod N)`.
   - Define `n_a(c) in Nbar` by `psi(a, c) mod M = n_a(c) s(c)`.
   - Then `zbar(h) = n(h) s(y(h))` with `n(h) = n_(x(h))(y(h))`.
3. **Output modulo `M`.** Lemma 3 applies at site `g` with `s_j = s(y(g m_j))`:

       T(z)(g) mod M = (sum_j L_j^(g,y)(n(g m_j))) U^(g,y).

   The `L_j` and `U` depend only on `y`.
4. **Flipping one data bit.** Let `x^h` be `x` with the bit at `h` flipped, keeping `y`.
   - Only `n(h)` changes, by `± v(h)` with `v(h) = n_1(y(h)) - n_0(y(h))`.
   - So the `Nbar`-part of `T(z)(g) mod M` changes by `± W_h(g)`, where `W_h(g) = sum over j with g m_j = h of
     L_j^(g,y)(v(h))`.
   - `W_h(g)` depends on `y` but not on `x`.
5. **Reading the flip.** The outputs `psi(tau(x)(g), y(g))` and `psi(tau(x^h)(g), y(g))` have the same ancilla.
   - If the two data bits are equal, the outputs are equal.
   - If they differ, the outputs have different data bits. Since `theta_M subset Delta_A`, they then lie in
     different `M`-cosets.
   - Hence `tau(x^h)(g) + tau(x)(g) = [W_h(g) != 0] =: e_h(g)`, which is independent of `x`.
6. **Locality.** `tau(x)(g)` depends only on `x` on `g S`, where `S` is a memory of `tau`. So `e_h(g) = 0` for
   `h not in g S`.
7. **Conclusion.**
   - The local rule `f : {0,1}^S -> {0,1}` of `tau`, on a finite memory `S`, satisfies
     `f(t + delta_i) = f(t) + e_i` for every coordinate `i` and every `t`, with constants `e_i`.
   - Hence `f(t) = f(0) + sum_i t_i e_i`, which is affine. `QED`

**Theorem A for solvable `Q`.**
- Take a chief series `1 = Q_0 < Q_1 < ... < Q_r = Q`.
- `theta_(Q_0)` is equality, which lies in `Delta_A`.
- `theta_(Q_r)` is all of `Q x Q`, which does not lie in `Delta_A`, since both data bits occur.
- Let `i` be the least index with `theta_(Q_i) not subset Delta_A`, and take `M = Q_(i-1)`, `N = Q_i`.
- For solvable `Q` the chief factor `N/M` is abelian, so Theorem A applies. `QED`

**Theorem B (every `Q`).** Suppose `T` realizes a non-affine `tau`.
- Choose a chief series of `Q` through `Sol(Q)`. Every factor below `Sol(Q)` is abelian.
- By Theorem A, the least crossing index is above `Sol(Q)`. So `theta_(Sol Q) subset Delta_A`: every
  `Sol(Q)`-coset lies in a single data fibre.
- Consequently `a o z` is a function of `z mod Sol(Q)`.
- Reducing the constants of `w` modulo `Sol(Q)` gives a `Q/Sol(Q)`-polynomial automaton `Tbar` with
  `Tbar(z mod Sol Q) = T(z) mod Sol Q`, and the data track `tau(x) = a o T(psi(x, y))` factors through `Tbar`.
  `QED`

**Sharpness (C).** Maurer–Rhodes: for a finite nonabelian simple group `S`, every function `S^k -> S` is a word
with constants. For `S = A_5` and `|B| = 30`, the map
`(q_1, ..., q_k) -> psi(f(a(q_1), ..., a(q_k)), b(q_1))` is therefore a word. Here `f` is the local rule of `tau`
on a memory containing `1`, with `q_1` read at `1`. This realizes every `tau`. `QED`

**Where the hypotheses were used.**
- **One data track `{0,1}`.**
  - Step 5 uses that there are exactly two data values, so "outputs differ" is a single bit read off from
    `W_h(g) != 0`.
  - With data `{0,1}^n` and `n >= 2`, a crossing can separate some tracks first, and the argument gives only a
    triangular structure.
- **Identity ancilla.** Step 2 uses that the ancilla at `h` is unchanged by a data flip, and step 5 compares
  outputs with equal ancilla.
- **Sitewise `psi`.** Lemma 2 needs single-site perturbations to stay single-site perturbations of `z`.

**Check.** `experiments/solvable-ancilla-realizations-2026-09-17/check_realizations.py` enumerates `Pol_2(Q)`
completely for ten groups of order at most 8, and a capped part of it for `A4`. It searches all realizations with memory `{1, m}`. The
realized rules are affine in every case, and the AND control is detected over every group (`results.txt`).
