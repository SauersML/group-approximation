---
rg: 2
id: sln-relators-force-linear-commutator-growth
kind: claim
title: In SL_n(Z) with n >= 5 every rank-k tuple has rank([u^L,v^L]-I) <= C_n k L for commuting root elements u, v, so cone-point and dislocation defects of the Wollmilchsau type cannot occur
distinct_from:
  sl2-relators-do-not-force-linear-commutator-growth: that builds rank-24 tuples of Z^2 x| SL_2(Z) with quadratic commutator growth; this proves that the relators of SL_n(Z), n >= 5, force linear growth, so that construction cannot extend to SL_5(Z).
  hs-dehn-modulus-bounded-by-dehn-function: that is the general area comparison for normalized HS defects; this applies the rank version of it to one family of words, after a dyadic shortcut filling that makes their area linear instead of quadratic.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung itself; this settles one sub-question on its long-root route (linear versus quadratic commutator growth) for g >= 5 and leaves the rung open.
---

**ESTABLISHED** (`sln-relators-force-linear-commutator-growth-proof`), conditional only on two
published theorems: Lubotzky-Mozes-Raghunathan (unipotents of `SL_n(Z)`, `n >= 3`, are
exponentially distorted) and Young (`SL_n(Z)`, `n >= 5`, has quadratic Dehn function). Unreviewed.

**Setting.** `Gamma = SL_n(Z)` with a fixed finite presentation `<S | R>`. A **rank-`k` tuple** is
`rho : S -> GL(d, C)` (unitary or not) with `rank(rho(r) - I) <= k` for every `r` in `R`, extended to
the free group. For commuting elementary matrices `u = e_ij`, `v = e_kl` (for example `u = e_13`,
`v = e_23`) put `phi(L) = rank(rho([u^L, v^L]) - I)`.

**Theorem.** For `n >= 5` there is `C_n` such that for every rank-`k` tuple, every `L >= 1` and
every commuting pair of elementary matrices `u, v`,

```text
rank(rho(u)^L - rho(W_L(u))) <= C_n k L,        phi(L) <= C_n k L,
```

where `W_L(u)` is a fixed word of length `O(log^2 L)` representing `u^L`. The reason is that
`Area([u^L, v^L]) <= C_n L`.

**Consequences.**

1. **The wave-3 question is answered: yes.** Adding the relators of `SL_5(Z)` to those of
   `P = Z^2 x| SL_2(Z)` turns the unbounded ratio `phi(L)/L = 12 L` of the Wollmilchsau tuples
   (`sl2-relators-do-not-force-linear-commutator-growth`) into `phi(L) <= C k L`. So no rank-`k`
   tuple of `SL_5(Z)` contains a `4 pi` cone-point or dislocation configuration for a commuting root
   pair that extends over `L ~ sqrt(d)` scales. The cone-point class of countermodels dies at
   `SL_5`.
2. **Deligne covers with `g >= 5`.** `SL_g(Z)`, embedded in the Siegel Levi of `Sp_(2g)(Z)`, lifts
   isomorphically to `Gamma_n`: `SO(g) -> U(g)` has `det = 1`, so the covering is trivial over
   `SL_g(R)`. Its relators have bounded area in the presentation of `Gamma_n`. So every rank-`k`
   sector tuple of `Gamma_n` has `phi(L) <= C_g k L` on every commuting pair of `SL_g`-root
   elements.
3. **Area lower bound in `P`.** With the Wollmilchsau tuples (`k = 24`, `phi = 12 L^2`), the rank
   inequality gives `Area_P([b^L, c^L]) >= L^2 / 2`. So in `P` the linear law fails for the
   same reason the filling is quadratic.

**Mechanism.** The rank defect of a trivial word is at most `k` times its area. The naive filling of
`[u^L, v^L]` is quadratic. The dyadic filling replaces `u^(2^j) u^(2^j)` by a shortcut for
`u^(2^(j+1))` at cost `O(j^2)`, which sums to `O(L)`. The remaining loop has length `O(log^2 L)`,
and its area is polylogarithmic by Young.

**Calibration.**
- Exact representations have `phi = 0`.
- In `P`, whose Dehn function is exponential, the bound fails, as the Wollmilchsau tuples show.
- In the Heisenberg group, `z` is only quadratically distorted, the dyadic sum diverges, and the
  method gives nothing.

**Open and exact gap.**
- **`g = 3, 4` (`SL_3`, `SL_4`).** The same proof works if the doubling loops
  `w_j w_j w_(j+1)^(-1)` have area `A_j` with `sum_j A_j / 2^j < infinity`, and the
  shortcut commutators have area `O(L)`. `SL_3(Z)` has exponential Dehn function (Epstein-Thurston),
  so this is open there.
- **Long-root pairs of `Sp_(2g)`.** They need a polynomial Dehn function for `Sp_(2g)(Z)`. It is
  reported quadratic for `g >= 5` (D. Cohen); this is not checked here.
- **Next step.** The theorem excludes the quadratic defects. It does not show that a pair with
  linear `phi` is close to a commuting pair: the slit origami
  (`slit-origami-z2-pair-has-rank-distance-half-l`) has commutator rank 2 and is still far from
  commuting. So the next falsifiable question is whether the `SL_5(Z)` relators also force
  `rank(rho(u)^L - rho(W_L(u))) = o(L)`, that is, a sublinear conversion defect. If they do, the
  long-root joint spectrum is rigid up to `o(L)` atoms.
