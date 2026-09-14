# hl-nh-quantum-reps: Deligne's Torelli character and quantum representations of Mod(S_2)

Lane date: 2026-09-13. Target: `non-hyperlinear-group`, through Deligne's triple cover `E_3` and the
Torelli-scalar quotient `deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2` (c5f8be311).

## 1. Landed

- **`genus-two-torelli-freely-generated-by-separating-twists`** (citation claim, route
  `genus-two-torelli-separating-twist-basis-citation`): Mess's Theorem D, quoted verbatim from
  Bestvina–Bux–Margalit, arXiv:0709.0287v1, extracted text lines 110–121.
- **`deligne-torelli-character-counts-separating-twists`** (claim, route
  `deligne-torelli-character-separating-twist-proof`):
  - (ST1) separating twists form one conjugacy class whose normal closure is `I(S_2)`;
  - (ST2) `c = epsilon * (separating-twist exponent sum) mod 3`, with `epsilon` a unit;
  - (ST3) a presentation of `E_3` with one corrected relator `t_s z^(-epsilon)`;
  - (ST4) `E_3` is hyperlinear iff `Mod(S_2)` has vanishing-defect almost representations with
    `||rho(t_s) - zeta I||_2 -> 0` for a primitive cube root `zeta`;
  - (ST5) no finite-dimensional unitary representation sends a separating twist to a primitive
    cube-root scalar.

## 2. Meyer's function (consistency check only, NOT landed)

Meyer's signature cocycle `tau` vanishes rationally on `Mod(S_2)`, so there is a unique Meyer function
`phi : Mod(S_2) -> Q` with `tau = delta phi`. Its restriction to the Torelli group is a homomorphism.

**Heuristic identification.** Suppose `[tau] = N [e]` for integer cocycles on `Sp_4(Z)`, where `e` is
the universal-cover class, up to 2-torsion. Then the argument of (TS1) with `Z_(3)` coefficients gives
`c = -(phi|_K)/N mod 3`, because `H^2(Mod(S_2); Z_(3)) = 0` and `Hom(Mod(S_2), Q) = 0`.

**The expected constants.** With the commonly quoted values:
- `N = +-4`;
- Endo's genus-two value `phi(separating twist) = -4/5`;
- this gives `c(t_s) = -phi(t_s)/N = +-1/5`, which is `+-2 mod 3` (since `5 = 2 mod 3` and `1/2 = 2 mod 3`), i.e. a unit, consistent with (ST2).

**Not pinned at source:** the relation `[tau] = +-4 e` (Barge–Ghys / Turaev type), and Endo's values
(Math. Ann. 2000). No claim is landed.

## 3. Quantum representations: separating twists are far from scalar

**Setup.** In the SU(2) level-`k` TQFT for genus two (BHMV/WRT conventions, `r = k + 2`,
`A = exp(i pi/(2r))`):
- the basis is the admissible colourings `(a, b, c)` of the dumbbell spine: loop colours `a` and `b`,
  bridge colour `c`, with `c` even, `c <= 2a`, `2a + c <= 2k`, and the same for `b`;
- the separating curve bounds the disc dual to the bridge;
- its twist acts diagonally by `theta_c = (-1)^c A^(c^2 + 2c)`, up to one global framing scalar.

For fixed even `c` there are `k - c + 1` admissible `a` (and the same for `b`), so colour `c` has
multiplicity `(k - c + 1)^2`. For a unitary `X` with eigenvalues `theta_j`, the normalized-HS distance to
the scalars is exactly

```text
min_lambda ||X - lambda I||_2^2 = 1 - |mean_j theta_j|^2.
```

This bound is independent of the global framing phase, so it bounds the distance to every scalar,
including `zeta I`.

**Computation.** Exact python on MSI, `research/artifacts/hl-nh-quantum-reps-2026-09-13/sepspec.py`, all
`k <= 400`; output `sepspec.json`, md5 `b709a95691999d324de6368ab6b705b9`, identical locally and on MSI.

| k | dim | abs mean eigenvalue | min scalar defect^2 |
|---|---|---|---|
| 1 | 4 | 1.000000 | 0.000000 |
| 2 | 10 | 0.800000 | 0.360000 |
| 3 | 20 | 0.648933 | 0.578885 |
| 4 | 35 | 0.653406 | 0.573061 |
| 5 | 56 | 0.662377 | 0.561257 |
| 8 | 165 | 0.541713 | 0.706547 |
| 10 | 286 | 0.510442 | 0.739449 |
| 16 | 969 | 0.427822 | 0.816968 |
| 32 | 6545 | 0.325380 | 0.894128 |
| 64 | 47905 | 0.241207 | 0.941819 |
| 100 | 176851 | 0.197111 | 0.961147 |
| 200 | 1373701 | 0.142691 | 0.979639 |
| 400 | 10827401 | 0.102488 | 0.989496 |

**Sanity checks.**
- The basis count `sum_(c even) (k - c + 1)^2` equals `(k+1)(k+2)(k+3)/6` for `k = 1..5` (4, 10, 20, 35,
  56). This matches the genus-two Verlinde dimension as recalled, not re-pinned.
- At `k = 1` only `c = 0` is admissible, so the separating twist is scalar. That level has finite image,
  and its scalar phase is not a primitive cube root compatible with a linear lift, as (ST5) forces.

**Reading.**
- Quantum representations are exact projective representations, but the separating twist spreads its
  spectrum. The minimal scalar defect tends to 1.
- So they give NO countermodel to (ST4) and are no evidence for hyperlinearity of `E_3`.
- They also give no lower bound for general almost representations: they are one specific family.

**Trust surface.**
- The BHMV basis, the admissibility rules and the twist eigenvalue formula are recalled from the standard
  conventions, not re-pinned at source.
- The lower-bound formula is elementary and exact for any unitary with those eigenvalues.

## 4. Asymptotic faithfulness does not give a dimension-free bound

Asymptotic faithfulness (Andersen; Freedman–Walker–Wang, not re-pinned) says that, for large level,
quantum representations separate any given non-central mapping class from the centre.
- That is a statement about one family of exact projective representations.
- A dimension-free lower bound on `||rho(t_s) - zeta I||_2` over ALL vanishing-defect almost
  representations would be the non-hyperlinearity of `E_3`, and by
  `translation-invariant-torus-gap-iff-finite-lcs-ru-gap` it would be tied to the general root.
- No mechanism for upgrading asymptotic faithfulness to such a bound was found. The upgrade would need
  some stability of `Mod(S_2)` in normalized-HS almost representations, and no such stability is known.

## 5. Exact gap

Decide whether vanishing-defect almost representations of `Mod(S_2)` can make one separating Dehn twist
almost a primitive cube-root scalar in normalized HS norm.
- **No:** a uniform positive lower bound. This makes `E_3` non-hyperlinear, a famous consequence.
- **Yes:** an explicit family, which must have unbounded blocks by `maslov-bounded-block-sector-gap` and
  can't be close to any quantum representation family (Section 3).
