---
rg: 2
id: bounded-blockwise-realizers-proof
kind: route
title: A bounded realizer makes a fixed nontrivial commutator fix most of the realized mass, against trace zero
target: bounded-blockwise-inner-realizers-fail-off-kernel
requires:
  - kun-expander-decomposition-formalized
---

Error terms are `o(|X_n|)` along `U`. For a block `B`, `e_B` denotes the number
of points of `B` where some fixed finite family of words disagrees with its
edited or approximately multiplicative version. By Kun's edit and the
asymptotic homomorphism property, `sum_B e_B = o(|X_n|)` for any fixed finite
family.

1. **A nontrivial commutator.** Fix `n in F`. Put `h = n^-1 g`. Since `g` is
   not in `N` and `n` is, `h != 1` and `h` is not in `N`. As `C_G(N) = 1` and
   `S` generates `N`, there is `s = s(n) in S` with `d = [h, s] != 1`. The
   finite family of words is `{n^-1, g, h, s, d}` over the finitely many `n` in
   `F`.

2. **The realizer becomes a centralizer on the block.** Let `B` be realized by
   this `n` and `c`. Off at most `e_B` points, `sigma(h) = sigma(n)^-1 sigma(g)`.
   So `sigma(h)` and `c` agree on a set `A ⊂ B` with
   `|A| >= (1 - eps)|B| - e_B`. Then `sigma(h)(A) = c(A)`, so `sigma(h)^-1` and
   `c^-1` agree on a set of the same size.

3. **The commutator almost fixes the block.** Write
   `sigma(d) = sigma(h) sigma(s) sigma(h)^-1 sigma(s)^-1` off `e_B` points. For
   `x in B`, follow `y = sigma(s)^-1 x`, then `sigma(h)^-1 y`, then `sigma(s)`,
   then `sigma(h)`. Replace each `sigma(h)^(±1)` by `c^(±1)` and each
   `sigma(s)` by `s_B`. The replacements fail on at most
   `2(eps|B| + e_B) + O(e_B)` points. After replacement the map is
   `c s_B c^-1 s_B^-1 = id_B`, since `c` commutes with `s_B`. So `sigma(d)`
   fixes at least `(1 - 2 eps)|B| - O(e_B)` points of `B`.

4. **Trace zero.** Summing over the blocks realized by `n`, the fixed-point
   count of `sigma(d)` is at least `(1 - 2 eps) m_n - o(|X_n|)`, where `m_n` is
   their total size. But `d != 1`, so `sigma(d)` has `o(|X_n|)` fixed points.
   As `eps < 1/2`, `m_n = o(|X_n|)`.

5. **Finitely many realizers.** The realized mass is at most the sum of `m_n`
   over the finitely many `n in F`, so it is `o(|X_n|)`. ∎
