# Class-sensitive definite shadows on the Promislow group (lane hl-kaplansky-class-shadows, 2026-09-14)

**Target.** Higman's integral unit conjecture on `P`
(`integral-unit-conjecture-torsion-free`). The lane executed survivor 1 of
`research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14.md`: find the input that
is definite only at the zero twisting class and push it against Case A.

**Verdict: partial, unreviewed.** Two claims landed. Neither decides the
conjecture.
1. `promislow-nonzero-twisted-classes-have-no-definite-shadows`. The twisting
   class is read off from two relator signs `kappa = (kappa_1, kappa_2)`. A minus
   sign forces a solution of `k h^2 k^-1 = -h^-2` in the target. In degree 2 over
   a formally real field this means `sqrt(2)` is in the centre. So `D(Z)`, and every
   such algebra, receives only the zero class.
2. `promislow-dihedral-ring-homomorphisms-are-the-three-shadows`. Every unital
   ring homomorphism `Z[P] -> D(Z)` is a shadow `A`, `B` or `C` followed by an
   endomorphism of `D(Z)`, or a sign character. So Case A units are exactly the
   units no homomorphism into `D(Z)` can see.

## Directive step 1: the shadows of the twisted rings

There are none. For `[c] != 0` no unital ring homomorphism `Z^c[P] -> D(Z)`
exists (claim 1, item 4).
- **Gardam's twisted unit.** It is seen only after adjoining `zeta_8`: the gauge
  map of `promislow-twisted-integral-rings-carry-gardam-units` item 5, followed by
  shadow `C`, sends `abar -> zeta_8 u` and `bbar -> -zeta_8 t^-1 u` into
  `D(Z[zeta_8])`. main already computed its images there (7, 10 and 10 terms, norm
  1, not monomial) in `research/artifacts/promislow-definite-line-shadows-2026-09-13.md` §2.
- **Which step uses `c = 0`.** Step 1 of
  `promislow-definite-line-shadow-parseval-proof`, the relator check. The shadow
  assignments satisfy both relators with value `+1`, which is `kappa = (1, 1)`.
  Steps 2–4 (kernel count, multiplicative norm, sum of squares) are about `D(Z)`
  and any homomorphism into it, so they are class-blind.

## Directive step 2: the invariant

- **The invariant.** It is `kappa`, the pair of signs of
  `bbar^-1 abar^2 bbar abar^2` and `abar^-1 bbar^2 abar bbar^2` in `Z^c[P]`.
  - It is gauge invariant, because each relator has even exponent sums.
  - It is multiplicative in `c`, via `gbar -> gbar (x) gbar'`.
  - It equals `((-1)^e_1, (-1)^e_2)` on the class `e_1 beta(rho_1) + e_2 beta(rho_2)`.
  - It is injective by a presentation argument on central extensions. This
    re-derives `|H^2(P; Z/2)| = 4` without Poincaré duality.
- **"Definite" means `kappa = (1, 1)`.** Only then can the relators hold in a
  group like `D(Z)^x`, where no `h, k` satisfy `k h^2 k^-1 = -h^-2`.
- **Degree-2 lemma** (claim 1, item 3). Let `A` have degree at most 2 over `F`.
  A solution forces `-1` to be a square in `F`, or `h^4 = -1`, and the latter
  forces `-1`, `2` or `-2` to be a square. Over formally real `F` only
  `sqrt(2) in F` remains.
- **`D(Z)`.** It sits in `D(Q(t))`, of degree 2 over `Q(t + t^-1)`. That field is
  formally real and lacks `sqrt(2)`, so `D(Z)` is rigid.
- **Nonzero classes.** Twisted assignments into `D(Z[zeta_8])` exist for all four
  classes, and `h = zeta_8 u` is the solution the lemma requires.

## Directive step 3: against Case A

Claim 2 shows that Case A (`v in epsilon + I_A cap I_B cap I_C`) is exactly
invisibility under all homomorphisms into `D(Z)`.
- **The shadows are exhausted.** Any refinement of the definite shadows that
  stays inside `D(Z)` is one of `e o A`, `e o B`, `e o C`, so it gives nothing new
  on Case A.
- **Other lines don't help.** Class-sensitive degree-2 targets on the other
  `K4`-fixed lines exist, but have infinite unit groups. On `x, y -> +1` the quotient
  is the group ring `Z[D_inf]`, and `1 + (1-a)b(1+a)` is a nontrivial unit
  (`n = (1-a)b(1+a)` has `n^2 = 0`).
- **No triviality theorem.** No statement of the form "every unit of `Z[P]` with
  support in a ball of radius `R` is trivial" follows from these inputs, and none
  was landed.

## Exact gap

Case A needs an input with two properties:
- **(i)** it sees the zero class: it fails for `Z^c[P]`, `[c] != 0`, e.g. by being
  unavailable over rings containing `zeta_8`, `i` or `sqrt(2)`;
- **(ii)** it does not factor through `D(Z)`.

Candidates, none known to work:
- a positivity or height statement on the degree-4 fibres of `Q[P]` that fails
  over `Z[zeta_8]`;
- a global integrality argument not decomposed into fibres.

Survivors 2 and 3 of the ideas artifact (the Bieberbach twisted census and the
radius-4 Case A certificate) are untouched.

## Checks

MSI, login node `ahl04`, `/usr/bin/python3.12` (3.12.13), exact integer
arithmetic, 0.36 s. Run in `/scratch.global/sauer354/hl-kaplansky-class-shadows/`.

| file | md5 |
|---|---|
| `hl-kaplansky-class-shadows-2026-09-14/class_shadow_check.py` | `51d959237ffcd5f2724a6410453a9fb5` (local and MSI agree) |
| `hl-kaplansky-class-shadows-2026-09-14/class_shadow_check-run.log` | `223c63a9c9b8b7ced8034680f0e5b2d1` (local and MSI agree) |

The log records:
1. **Relator signs** of the four models `s^(e_1 it) t^(e_2 jt) g` inside
   `R[P]`, `R = Z[s,t]/(s^4+1, t^4+1)`: `(+1,+1), (+1,-1), (-1,+1), (-1,-1)` for
   `(e_1,e_2) = (0,0), (0,1), (1,0), (1,1)`.
2. **All homomorphisms `P -> D(Z)^x`** with exponents `|m| <= 3`:
   - 4 sign characters, and 196 in each of the families RF, FR and FF;
   - each of those matched by `e o A`, `e o B` or `e o C` for an endomorphism
     found by search.
3. **Rigidity:** no `h, k` with `|m| <= 4` satisfy `k h^2 k^-1 = -h^-2` in `D(Z)^x`.
4. **Twisted homomorphisms** `Z^c[P] -> D(Z[zeta_8])` with relator values
   `zeta_8^(4 e_i)`, and the witness `h = zeta_8 u`.
5. **The unit** `1 + (1-a)b(1+a)` of `Z[D_inf]`, support 5.

## Not done

- **Literature.** No search beyond the repo and the sources cited by the claims
  already on main. The factorization of `X^4 + 1` and the reduced-trace argument
  are standard.
- **Degree 4.** A class-sensitive positivity statement on the degree-4 fibres
  was not attempted beyond the observation that the Hermitian trace identity is
  class-blind (`research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14.md`, idea 4).
