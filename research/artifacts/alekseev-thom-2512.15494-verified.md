# Alekseev--Thom arXiv:2512.15494 primary-source check

Checked 2026-08-25 from the current arXiv HTML of v1, whose displayed
manuscript date is 2026-08-24.

Source: Vadim Alekseev and Andreas Thom, *Remarks on approximability and
stability for groups*, arXiv:2512.15494v1.

The following statements were read from the primary text.

- Definition 3.1: `G` is stable in finite actions when, for every sofic
  approximation of `G`, its limit action is weakly contained in the class of
  finite `G`-actions.
- Lemma 3.2: for residually finite `G` and an asymptotic homomorphism
  `alpha_n:G->Sym(X_n)`, choose finite quotients `rho_n:G->H_n` injective on
  growing finite windows and set

  ```text
  theta_n(g)(x,h)=(alpha_n(g)(x), lambda_(H_n)(rho_n(g))(h)).
  ```

  Then `theta_n` is a sofic approximation, and the `alpha_n` action is a
  factor by projection to `X_n`.
- Theorem A(ii), restated as Theorem 3.4: in a short exact sequence
  `1->N->G->Q->1`, if `N` is Kazhdan, `G` is residually finite and stable in
  finite actions, then `Q` is stable in finite actions; in particular a
  sofic `Q` is residually finite.
- Introduction after Corollary C: the authors state that it is open whether
  there exists a residually finite group which is not stable in finite
  actions.

Scope fence: every inheritance theorem above is about a **normal kernel**
`N`.  It does not apply to the proper nonnormal subgroup
`SL_3(Z)<SL_3(Z[1/p])`.
