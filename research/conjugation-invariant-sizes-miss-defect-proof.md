---
rg: 2
id: conjugation-invariant-sizes-miss-defect-proof
kind: route
title: The realizer set of a compressed twist is a conjugate of the original realizer set
target: conjugation-invariant-sizes-miss-relative-defect
requires:
  - realized-relative-twists-embed-in-outer-twist-group
---

Notation as in the target; write `s = sigma(t)`.

1. **Realizer sets move by conjugation.** By items 1 and 2 of
   `realized-relative-twists-embed-in-outer-twist-group`, `eps_t([x])` is the
   class of `s^-1 x s`, and `s^-1 (M_s C_s) s = M_s C_s`. The second holds
   because `M` is normal in `G` and `sigma(G)` normalizes `C_s`. Hence

   ```text
   R(eps_t(q)) = s^-1 x s . M_s C_s = s^-1 (x M_s C_s) s = s^-1 R(q) s,
   ```

   and `F(R(eps_t(q))) = F(R(q))` by conjugation invariance of `F`. This is
   item 1.
2. **Trace zero.** For an injective trace-zero sofic representation, the
   fixed-point proportion of `sigma(z)` equals the canonical trace of `z`,
   which is `0` for `z != 1`. So the support proportion is `1`. This is
   item 2.
3. **Relative position.** Conjugation by `s` maps `R(q)` onto `R(eps_t(q))`
   and `Gamma_s` onto `sigma(t^-1 Gamma t)`, not onto `Gamma_s`.
   - Any quantity built from the pair `(R(q), Gamma_s)` that changes under
     `eps_t` changes because `Gamma_s` sits strictly inside
     `sigma(t^-1 Gamma t)`.
   - Every other ingredient is transported exactly, by step 1.
   - By item 3 of the source claim, `Q_s` depends on `sigma` only through the
     `S_U`-conjugacy class of `sigma|_Gamma`.
   This is item 3.
4. **No property (T) in items 1 and 2.** Steps 1 and 2 use only normality of `M`
   and the normalization of `C_s`. For hosts without rigid pairs, replace
   `C_s` by any subgroup normalized by `s`; the same computation applies.
