---
rg: 2
id: deligne-norm-parameter-group-embeds-in-ce-subgroup
kind: claim
title: Deligne's norm-parameter group lies in the Connes-embeddable Maslov subgroup, and the universal-cover lattice is hyperlinear exactly when that subgroup is the whole circle
distinct_from:
  maslov-ce-subgroup-classifies-finite-deligne-covers: that classifies the finite covers E_q by whether 1/q lies in E_CE; this compares E_CE with the operator-norm group P_op at every parameter, including irrational ones, and treats the infinite cyclic lattice E_infinity itself.
  deligne-hs-parameter-trace-threshold: that proves P_op <= P_2 and E_CE <= P_2 for the untraced HS group P_2 and leaves the comparison of P_op with E_CE open; this proves P_op <= E_CE.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is the fixed-parameter operator-norm gate at 1/3, which route deligne-opnorm-sectors-empty-from-hs-defect-gap reaches from the HS gap at 1/3; this is the inclusion at every parameter at once, and it turns non-hyperlinearity of E_infinity (not of E_3) into finiteness of P_op.
  sp4-finite-index-scalar-data-iff-hyperlinear-covers: that proves (FIC2), that a positive-dimensional E_CE makes E_x hyperlinear; this adds the converse for the Maslov class, so non-hyperlinearity of E_infinity is exactly finiteness of E_CE.
  dogon-sp2g-weak-ucp-nonhyperlinear: that makes E_infinity non-hyperlinear under weak ucp-stability of Sp_4(Z); this converts that conclusion into finiteness of the operator-norm group P_op.
  deligne-lattice-non-mf-forces-finite-parameter-group: that derives finiteness of P_op from non-MF of E_infinity; this derives it from the incomparable tracial statement, non-hyperlinearity of E_infinity, with no corner hypothesis.
---

**ESTABLISHED** (route `deligne-norm-parameter-group-embeds-in-ce-subgroup-proof`). Unreviewed.

**Setting.** `Gamma = Sp_4(Z)`, and `b` is the normalized integral covering cocycle of
`deligne-sep7-norm-parameter-closed-subgroup`. That is the cocycle for which
`E_infinity = Gamma x_b Z`, with product `(g,j)(h,l) = (gh, j + l + b(g,h))` and central generator `z = (e,1)`. It is
also the cocycle that `maslov-ce-subgroup-classifies-finite-deligne-covers` uses to define `E_CE`. Put
`c_theta = exp(2 pi i theta b)`, and write `E_infinity = Gamma~`. Define:
- `P_op` is the set of `theta` with operator-norm asymptotic `c_theta`-representations
  (`deligne-sep7-norm-parameter-closed-subgroup`);
- `E_CE` is the set of `theta` with `L_(c_theta)(Gamma)` Connes embeddable, that is, with canonical-trace
  `c_theta`-microstates (`maslov-ce-parameter-set-is-a-closed-subgroup`).

**Theorem.**
1. **(NCE1) Inclusion.** `P_op <= E_CE`.
2. **(NCE2) The lattice.** `Gamma~` is hyperlinear if and only if `E_CE = R/Z`.
   - More precisely: if `pi : Gamma~ -> U(M^w)` is any injective homomorphism into a matricial tracial
     ultraproduct, then `theta in E_CE` for every `theta` with `exp(2 pi i theta)` in the support of the spectral
     measure of `pi(z)`.
   - This support is never contained in a finite group of roots of unity.
3. **(NCE3) Tracial finiteness gives norm finiteness.** The following are equivalent:
   - `Gamma~` is not hyperlinear;
   - `E_CE` is finite;
   - some finite Deligne cover `E_q` is not hyperlinear.

   When they hold, `P_op` is finite, and `|P_op|` divides `|E_CE|`.

**Corollaries.**
- **(NCE4)** Each of the following makes `P_op` finite, with no corner hypothesis:
  - weak ucp-stability of `Sp_4(Z)`, equivalently its flexible HS-stability
    (`dogon-sp2g-weak-ucp-nonhyperlinear`, `kazhdan-weak-ucp-stability-is-flexible-stability`);
  - the LLP of `C^*(Sp_4(Z))`. In the contrapositive of `sp4-llp-failure-or-maslov-nonhyperlinear-extension`,
    `E_CE = R/Z` forces LLP failure, so LLP makes `E_CE` finite.

  Under the single instance `(CPE*)` of `commutant-projection-extraction`, finiteness of `P_op` is equivalent to
  non-MF of `Gamma~` (item 5 of `deligne-lattice-non-mf-forces-finite-parameter-group`). So under `(CPE*)`:

  ```text
  Gamma~ not hyperlinear  ==>  Gamma~ not MF.
  ```

  Without `(CPE*)` this implication is not formal; `deligne-lattice-norm-models-are-tracially-blind` shows why.
- **(NCE5) New decomposition of the flagship.** `deligne-triple-cover-exact-mf-radical` follows from two
  statements, each of which can fail on its own:
  - `deligne-universal-cover-lattice-is-not-hyperlinear`, a statement about one named Kazhdan lattice, equivalent
    to finiteness of `E_CE`;
  - `deligne-finite-parameter-group-has-period-prime-to-three`.

  This is route `deligne-triple-cover-via-lattice-non-hyperlinear`. The first prerequisite is implied by (and not known to imply)
  non-hyperlinearity of `E_3`, which already implies the flagship by
  `deligne-opnorm-sectors-empty-from-hs-defect-gap`. The reason: `E_3` non-hyperlinear means `1/3 notin E_CE`,
  whereas the first prerequisite only asks that `E_CE` be finite, with no control on its order.
- **(NCE6) Chain of parameter groups.** `P_mon <= P_op <= E_CE <= P_2`. Here `P_mon` is the monomial group of
  `deligne-monomial-parameter-group-is-governed-by-maslov-slope`, and `P_2` is the HS group of
  `deligne-hs-parameter-trace-threshold`. All four are closed subgroups containing `1/2`.

**What this does not do.** It does not decide whether `E_CE` is finite. It gives no information on the prime `3` in
`|P_op|`. The inclusion `P_op <= E_CE` can be strict as far as is known. Nothing here proves that a hyperlinear
`Gamma~` is MF.
