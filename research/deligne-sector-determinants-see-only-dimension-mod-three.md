---
rg: 2
id: deligne-sector-determinants-see-only-dimension-mod-three
kind: claim
title: Determinant, trace-log and winding invariants of Deligne sector models detect only the matrix dimension modulo three
artifacts:
  - research/deligne-sector-determinant-congruence-proof.md
distinct_from:
  exel-loring-mark-quantization: that is a programme for an infinite-order central mark whose Blocker 1 asks for a twisted form of Dadarlat's Theorem 1.1; this proves the twisted form for the order-three Deligne mark and shows its only output is a congruence on the dimension, so the programme gives nothing for E_3.
  matrix-corona-k1-vanishes: that shows a single marked unitary carries no corona K_1 class; this treats relative determinant data of words that fill H_2 classes, the shape that claim leaves open, and kills it for finite-order marks.
  deligne-sep8-first-order-tensor-threshold: that proves a dimension-free first-order lower bound in the twist parameter from a gap at one third; this is an unconditional dimension-dependent lower bound c/d in dimensions prime to three, which tends to zero and decides nothing.
  deligne-triple-cover-fd-central-invisibility: that excludes exact finite-dimensional representations with z nontrivial; this quantifies the determinant half of that obstruction for approximate models and shows it disappears after tripling the dimension.
  deligne-sector-siegel-spectrum-is-full-torus: that kills Siegel spectral separation; this kills determinant and index separation, a different invariant.
---

**THEOREM (ESTABLISHED).**  Let `Gamma = Sp_4(Z) = <S | R_0>` be a finite
presentation, `F = F(S)`, `R` the normal closure of `R_0`, and
`R' = R cap [F,F]`.  Let `b` be a normalized integral two-cocycle whose
reduction mod three gives Deligne's triple cover `E_3`.  Let
`Gamma~ = Z x_b Gamma`, and let `iota : F -> Gamma~` send `s` to `(0,s)`.
For `r in R` write `iota(r) = (k_r, e)`.  This defines a homomorphism
`k : R -> Z`.  For `theta in R/Z` put `c_theta = e(theta b)`, where
`e(t) = exp(2 pi i t)`.

- **(DC0) Some filling sees the mark.**  There is `r in R'` with
  `k_r` not divisible by three.
- **(DC1) Determinant congruence.**  Let `r in R'` be a word of length `L`
  and put `L_r = 2L - 1`.  There is a finite multiplication window `W_r`
  depending only on the word.  Let `U` be a map from the elements of
  `Gamma` used in `W_r` to `U(d)` with `U(e) = I`, and suppose
  `delta = max_(g,h) in W_r ||U(g)U(h) - c_theta(g,h) U(gh)||`
  satisfies `L_r delta <= 2`.  Then

  ```text
  dist(d theta k_r, Z) <= d L_r delta / 4.                          (DC1)
  ```

  At `theta = 1/3` or `2/3`, take `r` from (DC0).  Every operator-norm
  model in a dimension `d` prime to three then has
  `delta >= 4/(3 d L_r)`.
- **(DC2) Exact determinant data are consistent exactly when three
  divides d.**  For `d >= 1` the following are equivalent:
  - there is a homomorphism `chi : F -> T` with `chi(r) = e(d theta k_r)`
    for every `r in R`;
  - `d theta k_r` lies in `Z` for every `r in R'`.

  At `theta = 1/3` or `2/3` these hold iff `3 | d`.  When they hold, the
  tuple `U(s) = diag(chi(s), 1, ..., 1)` in `U(d)` has exactly the
  predicted determinant on every relator word.
- **(DC3) The normalized form carries no information.**  Under the
  hypotheses of (DC1), the normalized trace-log

  ```text
  tau_r(U) = theta k_r + (1/2 pi i) tr_d Log(e(-theta k_r) V_r)
  ```

  (principal logarithm; `V_r` is the word evaluated on `U`) lies in
  `(1/d) Z` and satisfies `|tau_r(U) - theta k_r| <= L_r delta / 4`.
  Integers `m_n` with `m_n/d_n -> theta k_r` exist for every sequence
  `d_n -> infinity`.  Equivalently, in a norm matrix corona
  `Q = prod M_(d_n) / sum M_(d_n)` with `d_n -> infinity` along the
  ultrafilter, the trace image of `K_0(Q)` is all of `R`.  So the
  de la Harpe--Skandalis determinant takes values in `R / R = 0`.

**Class kill: linear-characteristic separation.**  Call a separation argument
*linear-characteristic* when it works like this:

- **Invariant.**  It evaluates a determinant, a trace of a logarithm, an
  Exel--Loring or Dadarlat winding number
  `wn det((1-t) + t V_r)`, or a K_0/K_1 pairing on words in the model
  unitaries that fill `H_2` classes.
- **Win condition.**  It wins by showing that the integrality of that
  invariant is incompatible with the fractional central phases
  `e(theta k_r)`.

Every such argument dies at one step, "the determinant constraints are
inconsistent":

- **Unnormalized members.**  By (DC2) the exact constraints are consistent
  as soon as `3 | d_n`.  Every model sequence can be moved into that case
  without changing its defect by replacing `U_n` with `U_n tensor I_3`.
- **Normalized and tracial members.**  By (DC3) the target value group is
  `R`.

The only content that survives is the tradeoff in (DC1),
`d_n delta_n >= 4/(3 L_r)` in dimensions prime to three.  It tends to zero
and is compatible with MF.  In particular, the twisted form of Dadarlat's
Theorem 1.1 that `exel-loring-mark-quantization` requires in its
near-scalar case holds for the Deligne mark, and it proves nothing about
`E_3`.

**What survives.**  This theorem does not touch:

- spectral-multiplicity invariants that are not multiplicative in the word;
- vector-state and relative-(T) mechanisms;
- the matrix origin of models beyond their determinants.

The proof is `deligne-sector-determinant-congruence-proof`.
