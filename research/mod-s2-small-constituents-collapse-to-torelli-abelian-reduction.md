---
rg: 2
id: mod-s2-small-constituents-collapse-to-torelli-abelian-reduction
kind: claim
title: The tensor-word loss of a near-cube-root representation of Mod(S_2) equals its least weighted prime-to-three Torelli constituent, so the small-constituent weakening (SB) is equivalent to the Torelli-abelian reduction and not weaker
distinct_from:
  mod-s2-near-scalar-torelli-closure-dichotomy: that proves the dichotomy and the one-sided bound D(rho) <= n for constituents of rho itself; this proves the exact identity for D(rho) over the whole tensor category and draws the graph consequence that (SB) and the reduction are the same statement.
  mod-s2-prime-to-three-torelli-constituents-are-large: that proves n arcsin(eps/2) >= pi d_inf per constituent and presents (SB) as a strictly weaker replacement for the reduction in (PC5); this shows the replacement is equivalent to the reduction, so (PC5) is the trivial split.
  mod-s2-cube-root-reps-have-small-prime-to-three-constituents: that is (SB), still OPEN; this proves it equivalent to mod-s2-near-scalar-reps-reduce-to-torelli-abelian and does not decide either.
  mod-s2-jones-torelli-closure-is-su5: that proves the Jones Torelli closure is SU(5) and kills closure-functorial Torelli-abelianizations; this adds only the dimension calibration (C3) that the SB node asked for as its next test.
---

**ESTABLISHED** through `mod-s2-small-constituents-collapse-proof`. Unreviewed; no novelty claimed (it
follows from exterior powers and the dichotomy of `mod-s2-near-scalar-torelli-closure-dichotomy`).

**Setting.** This uses the notation of `mod-s2-near-scalar-torelli-closure-dichotomy`:
- `rho : M = Mod(S_2) -> U(d)` is honest, with `eps = ||rho(t_s) - omega I||`;
- `H = cl rho(K)` and `S = cl[H, H]`;
- `V_ab = (C^d)^(x a) (x) (conj C^d)^(x b)` for `a + b >= 1`;
- `D(rho) = min{a + b : 3 not| a - b, V_ab^S != 0}`;
- `c_ab` is the Torelli-abelian infimum. It equals `2 sin(pi d_inf)` by (TA1) of
  `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`, so (TAP) holds iff `c_ab > 0`.

Call an irreducible `H`-subrepresentation `W` of some `V_ab` **admissible** if `3` does not divide
`(a - b) dim W`. Its **weight** is `(a + b) dim W`.

**Statement.**

1. **(C1) Exact loss identity.** For every honest `rho`,
   ```text
   D(rho) = min { (a + b) dim W : W an admissible irreducible H-subrepresentation of some V_ab } .
   ```
   Both sides are `infinity` exactly in case (a), `omega I in S`. Consequently every admissible `W` satisfies
   ```text
   (a + b) dim W * eps  >=  c_ab  =  2 sin(pi d_inf) .
   ```
   The row `a = 1, b = 0` is the Torelli constituents of `rho` of dimension prime to three. On that row
   (PC2) of `mod-s2-prime-to-three-torelli-constituents-are-large` is sharper. It gives
   `eps >= 2 sin(pi d_inf / n)` where this gives `eps >= 2 sin(pi d_inf) / n`, and the ratio is at most
   `pi d / sin(pi d)`, which is below `1.008` at `d = 1/15`. The new content is the identity and the rows
   `(a, b) != (1, 0)`.
2. **(C2) Collapse of (SB).** The following are equivalent:
   - (i) `mod-s2-cube-root-reps-have-small-prime-to-three-constituents` (SB);
   - (ii) (SB_tw): if `1/3 in Z_hon`, then the infimum of `(a + b) dim W * arcsin(eps/2)` over honest
     `rho` with `eps < 2` and admissible `W` is `0`;
   - (iii) `mod-s2-near-scalar-reps-reduce-to-torelli-abelian`: `1/3 in Z_hon` implies `1/3 in Z_ab`.

   Hence (PC5) of `mod-s2-prime-to-three-torelli-constituents-are-large`, "gap iff (TAP) and (SB)", is the
   tautological split "`1/3 notin Z_hon` iff `1/3 notin Z_ab` and (`1/3 in Z_hon` implies `1/3 in Z_ab`)".
   The routes `mod-s2-opnorm-torelli-gap-via-small-constituents` and
   `mod-s2-opnorm-torelli-gap-via-finite-index-multipliers` have the same open content. The remark in (PC5)
   that (SB) is a weaker replacement for the reduction is false in the only sense that matters: the two
   statements are equivalent.
3. **(C3) Calibration at the fifth roots (the test the SB node left unrun).** Let `zeta` be a primitive fifth
   root of unity and `rho` one of Jones' rectangular representations with `x/pi` irrational. Then every
   irreducible `H`-subrepresentation `W` of every `V_ab` on which `zeta I` acts non-trivially, that is with
   `5 not| a - b`, has `5 | dim W`. At the same time `eps_zeta -> 0` as `x -> 0`, by (JC2) of
   `mod-s2-jones-torelli-closure-is-su5`. So the known infinite-image near-scalar family lies entirely on the
   failing side of the fifth-root analogue of (SB). The fifth-root reduction is nevertheless true, but only
   through the external characters `chi_zeta`, which do not come from `rho`.

## What this kills

- **Class.** Every argument for `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` or for the
  reduction that proceeds by locating a small admissible constituent. The constituent may sit in `rho`, in a
  Schur functor, in a tensor word, or in a sub- or quotient representation of these, and "small" means
  `o(1/eps)` in weight.
- **Invariant.** The determinant line `Lambda^(dim W) W` inside `V_(a dim W, b dim W)`, on which `H` acts by
  a character trivial on `S`.
- **Where every member dies.** Finding such a constituent is exactly `D(rho) eps -> 0`, which is exactly a
  Torelli-abelian approximant. The argument has no content beyond the reduction itself.
- **What survives.** Arguments for the reduction that are not constituent-dimension arguments:
  - excluding case (a) for small `eps`, which is residual (R-a), by some input that distinguishes `omega`
    from `mu_5`, as (C3) requires;
  - bounding `D(rho) eps` directly, which is residual (R-b), by non-dimension data;
  - deciding (TAP), the census route.

## Failure region, restated

If `1/3 in Z_hon` but `1/3 notin Z_ab`, then along every sequence witnessing `1/3 in Z_hon`, every admissible
`H_j`-constituent of every tensor word has weight at least `c_ab / eps_j`. Every Schur functor of `rho_j` is
included. So an irreducible `H_j`-constituent `W` of any `V_ab` either has `3 | (a - b) dim W` or has weight
at least `c_ab / eps_j`. Part (CD5) of the dichotomy node states this only for the row `(1, 0)`.
