---
rg: 2
id: deligne-twisted-reduced-mf-iff-group-mf-and-sp4-reduced-mf
kind: claim
title: A rational Maslov-twisted reduced C-star algebra of Sp4(Z) is MF exactly when its parameter is in P_op and the untwisted reduced algebra is MF
distinct_from:
  deligne-sep7-all-cover-mf-radical-classification: that classifies group MF of every finite Deligne cover through P_op; this classifies MF of the reduced C-star algebras of the covers and of the twisted fibres, and shows the only extra input is reduced MF of Sp_4(Z) itself.
  infinite-kazhdan-group-with-mf-reduced-cstar: that asks for any infinite Kazhdan group with MF reduced algebra; this proves that MF of any single rational twisted reduced algebra of Sp_4(Z), for instance at parameter 1/3, would answer that question with Sp_4(Z).
  mf-min-tensor-exact-mf-is-mf: that is the permanence of MF under spatial tensor products with an exact MF factor; this applies it twice, with Fell absorption, to move MF between the twisted fibres.
  thom-central-corner-criterion: that decomposes a finite central extension into twisted corners to test Connes embeddability of the group; this is about operator-norm MF of the reduced algebras, where the twisted corners are coupled to the untwisted one.
  deligne-lattice-non-mf-forces-finite-parameter-group: that relates group MF of the Deligne lattice to the size of P_op; this is a reduced-algebra statement at rational parameters and says nothing about the size of P_op.
---

**ESTABLISHED** (route `deligne-twisted-reduced-mf-iff-group-mf-and-sp4-reduced-mf-proof`).

**Setting.** `Gamma = Sp_4(Z)`, `b` the integral covering cocycle, `c_theta = exp(2 pi i theta b)` and `P_op` as in
`deligne-sep7-norm-parameter-closed-subgroup`. `E_q = Gamma x_b Z/q` is the degree-`q` Deligne cover. For a
multiplier `c`, `lambda_c(g) delta_h = c(g,h) delta_(gh)` on `l^2(Gamma)`, and `C*_r(Gamma, c)` is the C-star algebra
these unitaries generate. MF means embeddable, not necessarily unitally, in some `prod_n M_(d_n) / sum_n M_(d_n)`.

**Theorem.** For every rational `theta in Q/Z` and every `q >= 1`:

- **(R1)** `C*_r(Gamma, c_theta)` is MF iff both `theta in P_op` and `C*_r(Gamma)` is MF.
- **(R2)** `C*_r(E_q)` is MF iff both `E_q` is MF and `C*_r(Gamma)` is MF.
- **(R3)** The reduced parameter set `P_r = {theta in Q/Z : C*_r(Gamma, c_theta) is MF}` is either empty or equal to
  `P_op ∩ Q/Z`. Since `1/2 in P_op`, the following are equivalent:
  - `C*_r(Gamma)` is MF;
  - `C*_r(Gamma, c_(1/2))` is MF;
  - `C*_r(E_2)` is MF.

**At the triple cover.** Put `theta = 1/3`. By `deligne-sep7-all-cover-mf-radical-classification`, `1/3 in P_op` iff
`E_3` is MF, iff the flagship `deligne-triple-cover-exact-mf-radical` fails. So

```text
C*_r(Sp_4(Z), c_(1/3)) is MF   <=>   C*_r(E_3) is MF
                               <=>   (E_3 is MF)  and  (C*_r(Sp_4(Z)) is MF).
```

**Class killed: reduced (tempered) data cannot decide the flagship.** The invariant is the Fell absorption unitary
`W(xi ⊗ delta_h) = Theta(h) xi ⊗ delta_h`, which intertwines `Theta ⊗ lambda_tau` with `1 ⊗ lambda_(c tau)`.

1. *Refutation side.* Suppose an argument refutes the flagship by producing reduced-norm-faithful `1/3`-models: a
   strongly convergent sequence of `c_(1/3)`-projective asymptotic representations, or any MF embedding of
   `C*_r(Gamma, c_(1/3))` or `C*_r(E_3)`. It then also proves `C*_r(Sp_4(Z))` MF, which makes `Sp_4(Z)` a positive
   answer to the open root `infinite-kazhdan-group-with-mf-reduced-cstar`. Magee--de la Salle record that even
   `C*_r(SL_3(Z))` is not known to be MF. Every such argument dies at the step "the untwisted reduced algebra of
   `Sp_4(Z)` is MF".
2. *Proof side.* "`C*_r(Gamma, c_(1/3))` is not MF" is equivalent to (flagship) or (`C*_r(Sp_4(Z))` not MF). An
   argument that detects non-MF only through reduced-algebra norms therefore proves the flagship only together with
   the open statement `C*_r(Sp_4(Z))` MF. If that statement is false, the twisted non-MF holds for a reason that has
   nothing to do with the centre `C_3`. So such arguments give only the decomposition

   ```text
   flagship  <=  [C*_r(Sp_4 Z, c_(1/3)) not MF]  and  [C*_r(Sp_4 Z) MF],
   ```

   and each prerequisite can fail on its own. The first is implied by the flagship. The second is independent of it
   as far as anything on main shows.

So neither direction of the flagship can be settled through tempered data alone unless the same argument also
settles the open reduced MF question for `Sp_4(Z)`. Tempered data means norms in the regular representation, or in
representations weakly equivalent to it. An argument that avoids this must use non-tempered finite-dimensional
structure, such as honest finite quotients or the non-tempered congruence spectrum.

**Generality.** Nothing but exactness of `Gamma` and finiteness of the order of the multiplier is used. The same
equivalences hold for every countable exact group and every multiplier of finite order. For (R1, `<=`) the order
need not be finite.
