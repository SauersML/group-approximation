---
rg: 2
id: fj-family-reduces-to-finite-by-cyclic-with-coefficients
kind: claim
title: For every group and every additive category with group action, K-theoretic assembly relative to finite-by-cyclic subgroups is an isomorphism onto assembly relative to virtually cyclic subgroups (Davis–Quinn–Reich)
distinct_from:
  crossed-product-rings-inherit-fjc-with-additive-coefficients: that identifies the coefficient system and orbit values for crossed products and states the VCyc assembly under the conjecture; this is an unconditional theorem shrinking the family from VCyc to finite-by-cyclic subgroups, removing every D_∞-type (amalgam) orbit.
  regular-coherent-laurent-coefficients-kill-twisted-nil-terms: that computes one finite-by-cyclic orbit value (a skew Laurent ring); this says no other infinite virtually cyclic orbit values are needed.
---

**ESTABLISHED (literature import).** Route:
`dqr-finite-by-cyclic-reduction-citation`.

Let `G` be any group and `A` an additive category with right `G`-action. Let
`fbc` be the family of finite-by-cyclic subgroups. These are the subgroups that
surject onto a cyclic group with finite kernel: the finite subgroups, and the
groups `F ⋊ Z` with `F` finite. Then for every `n ∈ Z` the relative assembly map

```text
H_n^G(E_fbc G; K_A)  ->  H_n^G(E_VCyc G; K_A)
```

is an isomorphism.

Consequently, if `G` satisfies the `K`-theoretic Farrell–Jones conjecture with
coefficients in `A` relative to `VCyc`, then the assembly map
`H_n^G(E_fbc G; K_A) -> H_n^G(pt; K_A)` is an isomorphism for every `n`. This
is the composite of two isomorphisms.

**Source.** J. F. Davis, F. Quinn and H. Reich, *Algebraic K-theory over the
infinite dihedral group: a controlled topology approach*, arXiv:1002.3702. The
arXiv comments read "Accepted for publication by the Journal of Topology". The
e-print TeX source was read on 2026-09-18, and the passages are stored in
`experiments/leavitt-kh-2026-09-17/dqr-1002.3702-excerpts.txt`.

- The families: "$1 \subset \fin \subset \fbc \subset \vc \subset \all$
  consist of the trivial subgroup, the finite subgroups, the extensions of
  finite by cyclic subgroups (groups that surject onto a cyclic group with
  finite kernel), the virtually cyclic subgroups ..."
- Corollary `cor-reduce-fj`: "For any group $G$ and ring $R$,
  $H_n^G ( E_{\fbc} G ; \bfK_{R}) \to H_n^G (E_{\vc} G; \bfK_{R} )$ is an
  isomorphism."
- Remark `rem-coeff`: "Theorem~\ref{thm-main} holds also with coefficients,
  i.e; with $\bfK_R$ replaced by $\bfK_{\cala}$ and $K_n ( R\g )$ replaced by
  $K_n ( \cala \ast_{\g} \pt )$. Since the transitivity principle is a fact
  about equivariant homology theories, Corollary~\ref{cor-reduce-fj} also holds
  with coefficients and therefore in the fibered case, too."
- Section 2 explains where the coefficient version comes from: "The version of
  Theorem~\ref{thm-main} with coefficients in an additive category, mentioned
  in Remark~\ref{rem-coeff}, follows from Theorem \ref{thm-main-coeff-version}
  below by the inheritance properties proven in \cite[Corollary
  4.3]{Bartels-Reich(coefficients)}."

**Trust surface.**
- The coefficient version of the corollary is stated in a remark, with a
  one-line justification: the transitivity principle together with the
  coefficient version of Theorem `thm-main`. The proof of the latter is given
  in the paper's Section 2 through Theorem `thm-main-coeff-version`.
- The transitivity principle used there is cited by DQR as [FJ-isom, Theorem
  A.10] and [Lück–Reich survey, Theorem 65]. It was not re-read.
- The journal version was not checked.
