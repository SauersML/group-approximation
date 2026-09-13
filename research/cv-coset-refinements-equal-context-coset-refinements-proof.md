---
rg: 2
id: cv-coset-refinements-equal-context-coset-refinements-proof
kind: route
title: Goursat classes of the label pairs of a variable question are transit labels between its contexts, and a designated context gives the converse
target: cv-coset-refinements-equal-context-coset-refinements
requires: [cv-coset-refinements-are-edge-label-coset-systems, hidden-labels-import-cross-context-commutation, forbidden-pair-splits-are-central-rectangle-splittings]
---

Notation as in the target.

**(E1) Labels.**  Apply (P1)–(P3) and (P6) of
`cv-coset-refinements-are-edge-label-coset-systems-proof` to `R`.  This gives:
- supports `S_q`;
- labels `ell_e` on the context side and `ell'_e` on the variable side, both
  onto `L_e`;
- shared block sums `F_e^lambda`;
- readouts `psi_e` with `X_v = sum_lambda (-1)^(psi_e(lambda)) F_e^lambda`.

**(E2) Transit labels.**  Fix `v`, contexts `c != c'` containing `v`, and put
`e = (c,v)`, `e' = (c',v)`.
- **The image coset.**  `t |-> (ell'_e(t), ell'_(e')(t))` on `S_v` is a left
  translate of a homomorphism.  Its image `P` is a left coset `(g,g') T`, where
  `T <= L_e x L_(e')` projects onto both factors.
- **Goursat.**  `P` is a disjoint union of rectangles `C_j x C'_j`.
  - The `C_j` are the left cosets of `N_T = {lambda : (lambda,1) in T}`, which is
    normal in `L_e`.
  - The `C'_j` are the left cosets of the corresponding `N'_T`, normal in
    `L_(e')`.
- **The transit PVM.**  Put `m_j = sum_(t in S_v, ell'_e(t) in C_j) p_v^t`.  For
  `t in S_v`, `ell'_e(t) in C_j` iff `ell'_(e')(t) in C'_j`.  So

  ```text
  m_j = sum_(lambda in C_j) F_e^lambda = sum_(mu in C'_j) F_(e')^mu,
  ```

  and `m_j` is a function of `p_v`, of `p_c` (through `F_e`) and of `p_(c')`
  (through `F_(e')`).  Also `sum_j m_j = 1`.
- **Readouts.**  Every `(lambda, mu) in C_j x C'_j` is the label pair of some
  `t in S_v`.  So `psi_e(lambda) = beta_v(t) = psi_(e')(mu)`.  Hence `psi_e` is
  constant on `C_j`, with the same value `b_j` as `psi_(e')` on `C'_j`, and
  `X_v = sum_j (-1)^(b_j) m_j`.

**(E3) The context relation.**  For `s in S_c` let `j_c(s)` be the class of
`ell_e(s)`, and for `s' in S_(c')` let `j_(c')(s')` be the class of `ell_(e')(s')`.
Put

```text
R^v_(cc') = {(s,s') in S_c x S_(c') : j_c(s) = j_(c')(s')}.
```

- **It is a coset.**
  - `j_c` is `ell_e` followed by the quotient `L_e -> L_e/N_T`.  So
    `j_c(s_c k) = x sigma(k)` for a homomorphism `sigma` into `Q = L_e/N_T`.
  - Likewise `j_(c')(s_(c') k') = x' sigma'(k')`, after identifying the classes
    through Goursat's isomorphism.
  - So `R^v_(cc')` has the form `{(s_c k, s_(c') k') : sigma(k) = b sigma'(k')}`.
  - It is nonempty, since each class is realized on `S_v` and the labels are
    onto.
  - By the computation in (P7) of the normal-form proof, it is a left coset of
    `{(k,k') : sigma(k) = sigma'(k')}`.
- **Acceptance.**  On `R^v_(cc')`,
  `beta_c(s)_v = psi_e(ell_e(s)) = b_j = psi_(e')(ell_(e')(s')) = beta_(c')(s')_v`.
- **It holds in `A(R)`.**  We have `p_c^s = p_c^s m_(j_c(s))` and
  `p_(c')^(s') = m_(j_(c')(s')) p_(c')^(s')`, and `p_c` vanishes off `S_c`.  So
  `p_c^s p_(c')^(s') = 0` off `R^v_(cc')`.

**(E4) Assembling `R^ctx`.**  For contexts `c != c'`, let `R^ctx_(cc')` be the
intersection of the relation `R_(cc')` of `R` with every `R^v_(cc')` for
`v in c ∩ c'`.
- **Nonempty.**  If the intersection were empty, every `p_c^s p_(c')^(s')` would
  vanish in `A(R)`.  Then `p_c = 0` and `A(R) = 0`.  So `R^ctx_(cc')` is a
  nonempty left coset.
- **A refinement.**  Its pairs agree on `c ∩ c'` by (E3).  So, with `K_c` and
  `beta_c` taken from `R`, `R^ctx` is a coset refinement of `G_B`.
- **The homomorphism.**  Every relation of `R^ctx` holds in `A(R)`.  So
  `p_c |-> p_c` defines `A(R^ctx) -> A(R)`.
- **Pushforwards.**  Both pushforwards of `A(B)` are given by the context PVMs,
  so they agree.

This proves (EQ1).

**(E5) Designated contexts.**  Given `R^ctx`, choose `c_v ∋ v` for every variable.
- **The refinement `R^cv`.**
  - Put `K_v = K_(c_v)` and `beta_v(t) = beta_(c_v)(t)_v`.
  - On `(c_v, v)` take the diagonal coset.
  - On `(c,v)` with `c ∋ v`, `c != c_v`, take the transpose of `R^ctx_(c_v c)`.
  - Take the full product on every other pair.
- **Acceptance.**  A pair `(t,s)` in `R^ctx_(c_v c)` agrees on `v`, so
  `beta_c(s)_v = beta_v(t)`.  The diagonal is accepted by the definition of
  `beta_v`.
- **The homomorphism.**  `p_c |-> p_c` and `p_v |-> p_(c_v)` respect every
  relation.
  - The diagonal becomes orthogonality inside one PVM.
  - The other relations become relations of `R^ctx`, or their adjoints.

This proves (EQ2).

**(E6) Traces.**  A tracial state on `A(R)` or on `A(R^ctx)` pulls back along the
homomorphism of (EQ1) or (EQ2).  The two pushforwards of `A(B)` agree, so the
lift persists.  This proves (EQ3).

**(E7) The corollary.**  Suppose `tau` lifts through a refinement of `G_cv(B(G))`.
- By (EQ1), it lifts through a coset refinement of the one-hot/NAND context
  game.
- In the GNS algebra of that lift:
  - Corollary 2 of `hidden-labels-import-cross-context-commutation` gives the
    split (FS) for every forbidden pair.
  - `forbidden-pair-splits-are-central-rectangle-splittings` turns (FS) into
    (CS), which is intrinsic to `N_(qq') = W*(P_q, P_(q'))`.
  - Over all forbidden pairs of `(q,q')`, (CS) is (RCS).
- These pair algebras are those of `tau` itself, since the restriction of a
  faithful trace generates the same von Neumann algebra.
- The factor case is Corollary 2 of the same node.
