---
rg: 2
id: mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors
kind: claim
title: Exact representations of Mod(S_2) with vanishing Torelli-scalar defect are finite-dimensional character approximations of the Deligne sector traces, and they make the genus-two triple cover hyperlinear
artifacts:
  - research/artifacts/hl-nh-deligne-extension-2026-09-14.md
distinct_from:
  deligne-torelli-character-counts-separating-twists: that is the almost-representation dictionary (ST4) and the exact exclusion (ST5); this treats genuine finite-dimensional representations of Mod(S_2), identifies the limits of their characters, and adds a conditional converse and a finite-image floor.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that characterizes non-hyperlinearity through all almost representations of E_3; this is a trace dictionary for the smaller class of exact representations of Mod(S_2).
  deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2: that excludes exact Torelli-scalar representations (TS4); this measures how close exact representations can come, in normalized Hilbert-Schmidt norm, and what their limits are.
---

**ESTABLISHED** through `mod-s2-exact-models-deligne-sector-limits-proof`. Unreviewed; no novelty
claimed.

**Notation.** As in `deligne-torelli-character-counts-separating-twists`:
- `M = Mod(S_2)`, `K = I(S_2)` its Torelli group, `t_s` a separating Dehn twist;
- `c : K -> Z/3` Deligne's invariant character, `epsilon = c(t_s)`, a unit;
- `omega = exp(2 pi i/3)`, `q : M -> E_3` the quotient map of (TS1), `z` the covering generator;
- `A_omega = C*(E_3)/(z - omega)`, and `T_omega(M)` the set of tracial states `tau o q` on `C*(M)` with
  `tau` a tracial state of `A_omega`;
- `||X||_2 = tr_d(X* X)^(1/2)` with `tr_d` the normalized trace;
- `Char_fd(M)` the set of normalized characters `tr_d o rho` of finite-dimensional unitary
  representations `rho` of `M`, and `cl Char_fd(M)` its closure for pointwise convergence on `M`.

For a finite-dimensional unitary representation `rho` of `M` put

```text
delta(rho) = || rho(t_s) - omega^epsilon I ||_2 .                         (XD)
```

It does not depend on `s`, since separating twists are conjugate (ST1). Complex conjugation `rho -> rho-bar`
exchanges `omega^epsilon` and `omega^(-epsilon)`, so the infimum below is the same for both cube roots.

**Statement.**

1. **(E1) Trace dictionary.** For finite-dimensional unitary representations `rho_n`,
   `delta(rho_n) -> 0` iff every pointwise cluster point of `tr o rho_n` lies in `T_omega(M)`. Hence
   ```text
   inf_rho delta(rho) = 0   iff   T_omega(M) meets cl Char_fd(M)
                            iff   tau'_+ or tau'_- lies in cl Char_fd(M),
   ```
   where `tau'_(+-)(m) = eta_(+-)(q(m))` if `q(m)` is central in `E_3`, and `0` otherwise, and `eta_+`,
   `eta_-` are the two central characters of `E_3` extending `z -> omega`.
2. **(E2) Sufficiency.** If `inf_rho delta(rho) = 0`, then `E_3` is hyperlinear. In that case
   `deligne-central-mark-hs-collapse` is false. Higher-genus covers are not affected, because
   approximation properties only propagate downward in genus
   (`deligne-cover-hyperlinearity-is-monotone-in-genus`).
3. **(E3) Conditional converse.** If `M` is flexibly Hilbert–Schmidt stable, then `E_3` hyperlinear
   implies `inf_rho delta(rho) = 0`.
4. **(E4) Finite-image floor.** For a finite-index normal subgroup `N` of `M`, let `l(N)` be the least
   `sum_j |e_j|` over products `prod_j g_j t_s^(e_j) g_j^(-1)` that lie in `N` and have
   `sum_j e_j != 0 mod 3`. This is finite by (TS2) and (ST2). Every representation factoring through
   `M/N` satisfies
   ```text
   delta(rho) >= sqrt(3) / l(N).
   ```

**Reading.** Deligne's invisibility (TS4) says `delta(rho) > 0` for every `rho`. The present claim
identifies the uniform question `inf delta > 0` as the non-membership of the two sector traces in the
closure of finite-dimensional characters of `Mod(S_2)`. It lies between the exact statement and the
terminal Torelli-scalar gap of (ST4): the terminal gap implies it, and it implies the terminal gap if
`Mod(S_2)` is flexibly HS-stable. The OPEN uniform target is `mod-s2-exact-representations-have-a-torelli-scalar-gap`.
