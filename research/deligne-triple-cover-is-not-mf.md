---
rg: 2
id: deligne-triple-cover-is-not-mf
kind: claim
title: Deligne's triple cover of Sp4(Z) is not MF
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
  - research/artifacts/deligne-sector-tensor-camouflage-2026-08-21.md
distinct_from:
  deligne-central-mark-hs-collapse: that asks for normalized-Hilbert-Schmidt collapse and is equivalent to non-hyperlinearity of E_3; this asks only for failure of operator-norm MF approximation and is strictly the MF question.
  deligne-triple-cover-fd-central-invisibility: that concerns genuine finite-dimensional representations; this excludes faithful operator-norm asymptotic representations, which is the unproved upgrade.
---

For Deligne's central extension

```text
1 -> <z>=Z/3 -> E_3 -> Sp_4(Z) -> 1,
```

the group `E_3` is not MF in the norm-matrix-corona sense.

By `deligne-triple-cover-finite-residual-is-center` and
`universal-mf-quotient`, this is equivalent to each of

```text
z in Rad_MF(E_3),
Rad_MF(E_3) = <z> = C_3.                                (DMF1)
```

Indeed `Rad_MF(E_3) <= Res_fin(E_3)=C_3`, while a non-MF countable group has
nontrivial MF radical.  Since `C_3` has prime order, there is no intermediate
subgroup.

## Attempts

- **Exact representations stop one topology too early.**  Deligne plus
  Malcev proves that every genuine finite-dimensional representation kills
  `z`, but MF radical membership quantifies over operator-norm asymptotic
  representations.  `fd-mark-stability-forces-mf-invisibility` explains the
  missing stability hypothesis, and no such stability theorem is known here
  for `E_3`.
- **Do not substitute the HS endpoint.**  Universal normalized-HS collapse
  of `z` is `deligne-central-mark-hs-collapse`, which
  `deligne-sector-gap-is-exactly-nonhyperlinearity` identifies with the
  stronger open assertion that `E_3` is non-hyperlinear.  HS-small exceptional
  central sectors may still have operator norm one, so that claim cannot be
  silently used as an operator-norm proof.
- **Literature boundary.**  Bachner--Dogon--Lubotzky, *On L1-approximation of
  groups*, arXiv:2508.17392v3, Proposition 1.5, gives non-MF only under the
  additional operator--HS stability condition and explicitly presents it as
  a potential approach to the MF question.  No theorem in that source proves
  this fixed triple cover non-MF.
- **Siegel spectral separation is dead (swarm-0917, entropy-measure).**
  `deligne-sector-siegel-spectrum-is-full-torus` proves that in every unital
  representation of a nontrivial sector `A_omega` (exact, corona,
  ultraproduct, regular) the Siegel radical `Sym_2(Z)` has joint spectrum
  all of `T^3`, every long-root lift has spectrum `T`, and every trace
  induces Haar measure.  Invariant: (Siegel spectrum, trace measure).  Every
  congruence-torsion / Magee--de la Salle transplant, quasi-unipotent
  eigenvalue bound, or invariant-measure rigidity argument dies at the step
  "the model has non-full, atomic, or non-Haar Siegel data", which is false
  for every representation.  The finite branch is empty because it would
  give a finite quotient seeing `z` (Margulis NST plus the Deligne residual).
  Survivors: vector-state atoms (the induced representation from
  `s(NU) x <z>` has invariant vectors), relative-(T) corners, and the matrix
  origin of models.  Artifact: `research/artifacts/deligne-sector-siegel-spectrum-2026-09-17.md`.
- **Semiclassical counter-models from finite-orbit symplectic actions are
  dead (swarm-0917, quantization).**  This is the natural source of
  operator-norm asymptotic models with non-finite-dimensional multipliers,
  aimed at refuting this claim.  The construction takes Berezin--Toeplitz
  or Zelditch quantized contact transformations of a quantizable symplectic
  action of `Sp_4(Z)` on a compact integral `(X, omega)`.  The leading
  multiplier has the form `omega = (prequantum lift class)^k *
  (Bargmann composition factor) * delta(f)`, with `f_g : X -> T` symbol
  phases.
  - *Invariant:* the class of the leading multiplier restricted to a
    finite-index stabilizer.
  - *Step where it dies:* suppose the action has a finite orbit, so a
    finite-index `Gamma'` fixes some `x_0`.
    - Evaluating the symbol identity at `x_0`, the prequantum lifts act on
      `L^k_(x_0)` by a character, so they give a coboundary.
    - The phases `f_g(x_0)` give a coboundary.
    - The composition factor is the metaplectic cocycle of the isotropy map
      `Gamma' -> Sp(T_(x_0) X)` in the Bargmann model, with values `+-1`.
    - Hence `omega^2|Gamma'` is a coboundary.
    - By `virtually-two-torsion-multipliers-miss-deligne-third` (VT2), no
      such model, after any rephasing, is a `c_1`- or `c_2`-sector model.
  - *Covered examples:* linear and affine actions on `T^4` (rational
    points), nilmanifold and cat-map quantizations, Weil-type theta
    representations (also finite-dimensional), and actions through finite or
    compact quotients.
  - *Hypothesis (not proved here):* that the leading symbol of
    `T_g T_h T_(gh)^*` at a common fixed point is the product of the pointwise
    symbols with the linearized Bargmann (metaplectic) composition factor.
    This is standard Toeplitz/FIO symbol calculus (Zelditch 1997, Charles
    2006), but no verbatim citation is recorded here.
  - *Survivors:* only quantizable symplectic actions of finite-index
    subgroups of `Sp_4(Z)` without finite orbits (Zimmer-exotic), or
    constructions not governed by a stabilizer-evaluated symbol calculus.
