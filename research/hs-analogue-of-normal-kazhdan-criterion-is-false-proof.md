---
rg: 2
id: hs-analogue-of-normal-kazhdan-criterion-is-false-proof
kind: route
title: Feed the sofic models of the Clifford witness to the two-norm statement and measure the central involution
target: hs-analogue-of-normal-kazhdan-criterion-is-false
requires:
  - sofic-non-mf-witness
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

## Why sufficient

**The configuration.**  In `W = Cl(X) x| V`, identify
`Gamma = Z^3 x| SL_3(Z)` with its level-zero copy in `V`, let `t` be the
stable letter of the ascending HNN extension, so `t Gamma t^-1 <= Gamma`,
and let `c` be the lamp at the root coset `Gamma in X`; `c` centralizes
`Gamma`.  For `a in Gamma` with `a not in t Gamma t^-1`, the lamps
`x = t c t^-1` and `y = a x a^-1` sit at distinct cosets, so
`[x, y] = epsilon`, and `d = [t c t^-1, a] = x y` satisfies
`d^2 = x y x y = [x, y] = epsilon`.  Thus `epsilon in D_W(Gamma)`.  This
is the manuscript's `prop:clifford-self-embedding`, and it is a pure
group identity.  `Gamma` is Kazhdan, `<epsilon>` is central of order two,
hence normal and Kazhdan.  Every hypothesis of the criterion holds.

**The two-norm asymptotic representation.**  By the prerequisite `W` is
sofic: there are maps `sigma_n : W -> Sym(d_n)` with
`d_H(sigma_n(gh), sigma_n(g) sigma_n(h)) -> 0` for all `g, h` and
`d_H(sigma_n(g), id) -> 1` for all `g != 1`, `d_H` the normalized Hamming
distance.  Let `V_n(g)` be the permutation matrix of `sigma_n(g)`.  For
permutations `pi, rho`,

```text
||P_pi - P_rho||_2^2 = (1/d) #{ i : pi(i) != rho(i) } * 2 = 2 d_H(pi, rho),
```

so `||V_n(gh) - V_n(g) V_n(h)||_2 -> 0`: `(V_n)` is a normalized-HS
asymptotic representation of `W`.

**The witness survives.**  With `g = epsilon != 1`,

```text
||V_n(epsilon) - 1||_2^2 = 2 d_H(sigma_n(epsilon), id) -> 2,
```

which is `(HS1)`.  So the conclusion of (HS) fails for `k = epsilon`.

**The mechanism, for the record.**  `(HS2)` is the triangle inequality
for the upper bound and the unit vector `xi = sqrt d E_12`, on which
`Ad(diag(-1,1,..,1))` acts by `-1`, for the lower bound.  The vectors
`sqrt d E_12` are not uniformly operator bounded, which is exactly the
gap between operator-norm and two-norm control of conjugation.  Nothing
else is used: no cocycle, no weighted norm, no rank metric.
