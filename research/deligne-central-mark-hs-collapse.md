---
rg: 2
id: deligne-central-mark-hs-collapse
kind: claim
title: Vanishing HS presentation defect forces the Deligne triple-cover central mark to collapse
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  hyperlinear-hs-stable-is-residually-finite: that repairs every generator of a hyperlinear microstate to an exact same-dimensional representation; this asks only that one named central word converge to the identity, with no nearby representation required.
  hs-schur-toeplitz-root-defect-collapse: that collapses an engineered Toeplitz/Steinberg root mark through coefficient recurrence; this is the analogous one-word target for Deligne's arithmetic order-three central mark.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that obstructs local HS stability of any infinite hyperlinear property-T group; this claim is much weaker than local stability and is tailored to a single explicit finite presentation.
---

For the explicit triple-cover extension

```text
1 -> <z>=Z/3 -> E_3 -> Sp_4(Z) -> 1,
```

fix any finite presentation containing the central word `z`.  Every sequence
of unitary tuples whose normalized-HS defects on the defining relators tend to
zero satisfies

```text
||phi_n(z)-I||_(2,d_n) -> 0.                              (DCM1)
```

No correction of the other generators is required.

For this particular cover, `deligne-sector-gap-is-exactly-nonhyperlinearity`
shows that `(DCM1)` is nevertheless equivalent to non-hyperlinearity itself.
If collapse fails, central-sector cutting produces a nontrivial projective
almost representation; tensoring it with canonical quotient microstates
makes the whole cover hyperlinear.  Hence the one-word formulation reduces
the number of words to control, but not the logical strength of the terminal
claim.

## Attempts

- **Central-character cut.** `finite-central-hs-sector-decomposition` reduces
  a counterexample to positive asymptotic dimension in the `alpha` or
  `alpha^2` projective sector of `Sp_4(Z)`.  Thus
  `maslov-mod3-projective-defect-gap` is a clean sufficient condition.
- **Do not prove full stability unless forced.**  Deligne already kills the
  mark in every exact finite-dimensional representation.  Repairing every
  generator throws away information and imports the whole Becker--Lubotzky
  instability wall; `(DCM1)` needs only a one-word estimate.
- **Property-T fallback.**  Since `E_3` is a finite central extension of the
  rank-two lattice `Sp_4(Z)`, it has property (T).  Proving local HS stability
  of `E_3` would also imply non-hyperlinearity by
  `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, but it is a strictly
  stronger target than `(DCM1)`.
- **Genus two is the strongest instance (2026-09-13, ex-nh-deligne-hs).**
  - `E_3` embeds in the triple cover of `Sp_(2g)(Z)` for every `g >= 2`, with `z -> z`
    (`deligne-cover-hyperlinearity-is-monotone-in-genus`). So `(DCM1)` propagates upward in genus,
    and nothing established at higher genus comes back down.
  - The weakest triple-cover target is `deligne-stable-triple-cover-is-not-hyperlinear`, which also
    gives `non-hyperlinear-group`.
- **Unnormalized collapse holds at genus at least 3, not here.**
  - `deligne-symplectic-covers-are-not-schatten-approximated`: for `g >= 3` the mark dies in every
    Schatten-p asymptotic homomorphism, `p <= 2`. Every nontrivial sector tuple in `U(d)` has
    normalized relator defect `>= delta d^(-1/2)`.
  - `(DCM1)` asks for exponent `0` instead of `1/2`.
  - The proof uses Frobenius stability (`blsw-real-lattice-frobenius-stability`, rank at least 3),
    which is unknown for `Sp_4(Z)`.
  - The two-norm argument (`bdl-deligne-type-two-norm-inapproximability`) cannot reach the
    normalized norm: one eigenvalue costs `d^(-1/2)` there.
  - What `(DCM1)` needs in the language of `kazhdan-commutant-compression-stability-is-finitary`
    is rounding to genuine representations inside the nontrivial sector. Malcev replaces
    localization. See `research/artifacts/deligne-hs-metric-ladder-2026-09-13.md`, Section 3.
- **Relocation to Mod(S_2) (2026-09-13, lane hl-nh-deligne-torus).**
  - `deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2`: `H^2(Mod(S_2); Z/3) = 0`, so the
    pullback of `E_3` to `Mod(S_2)` splits.
  - This gives `E_3 = (Mod(S_2) x Z/3) / L_c` for an invariant Torelli character `c : I_2 -> Z/3`
    that is nonzero on every finite-index part of `I_2`.
  - `(DCM1)` fails iff `Mod(S_2)` has vanishing-defect almost representations in which finitely many
    Torelli normal generators are almost scalar, with phases `zeta^(c(k_i))`.
  - No finite-dimensional representation of `Mod(S_2)` does this exactly.
  - The reformulation adds no rigidity by itself: a uniform lower bound on the Torelli-scalar defect
    is the same terminal problem.
- **Seeded descents, all relators (2026-09-13).**
  - `research/artifacts/sp4-twist-descent-all-relator-evaluation-2026-09-13.md`: the `d = 20, 30, 40`
    minima reach `0.3221`, `0.3249` and `0.3400` on all `304,412` relators.
  - All three are above the exact abelian bar `0.306783`, so the sub-bar working-set values were
    sampling artifacts.
  - The instrument stays blind to large-block countermodels (`maslov-bounded-block-sector-gap`).
