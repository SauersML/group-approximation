---
rg: 2
id: classical-width-from-finite-field-linear-sofic-dichotomy
kind: route
title: Pass from F_q to F_p by restriction of scalars and apply the fixed-characteristic special linear and isometry theorems
target: non-linear-sofic-simple-groups-bounded-width-in-classical-groups
requires: [simple-group-psl-width-is-finite-field-linear-soficity, simple-group-classical-width-finite-field-linear-soficity]
---

Let `q = p^e`.

1. **`F_q`-linear soficity is `F_p`-linear soficity.**
   - Rank does not change under field extension, so `F_p`-linear sofic implies `F_q`-linear sofic.
   - Restriction of scalars embeds `GL_n(F_q)` in `GL_(ne)(F_p)`, multiplying rank and dimension by `e`,
     so the normalized rank metric is preserved. So `F_q`-linear sofic implies `F_p`-linear sofic.

   So "not linear sofic over `F_q`" is "not `F_p`-linear sofic".
2. **Special linear groups.** Item 2 of `simple-group-psl-width-is-finite-field-linear-soficity` gives
   one `K` for every `SL_n(p^f)/Z_0` and every tuple. This includes `SL_n(q)` and `PSL_n(q)`.
3. **Isometry groups.** The fixed-characteristic statement of
   `simple-group-classical-width-finite-field-linear-soficity` gives one `K` for every
   `Sp_n(p^f)`, `SU_n(p^f)` and `Omega^+-_n(p^f)` whose central quotient is simple, and their central
   quotients. `SU_n(q)` sits in `GL_n(F_(q^2))`, which has the same characteristic.
4. **Conclusion.** `K(G, q)` is the maximum of the two constants, and it depends only on `G` and `p`.
