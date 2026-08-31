---
rg: 2
id: alekseev-thom-flexible-p-quotient-permanence
kind: route
title: Descend corrected permutation actions through the kernel orbit set
target: flexible-p-stability-passes-to-fg-normal-quotients
requires: []
---

Source: Vadim Alekseev and Andreas Thom, *Remarks on approximability and
stability for groups*, [arXiv:2512.15494v1](https://arxiv.org/abs/2512.15494),
Theorem 2.6 (equivalently Theorem A(i)).

Given an asymptotic homomorphism `sigma_n:Q -> Sym(X_n)`, pull it back along
`G -> Q`. Flexible P-stability of `G` corrects the pullbacks to genuine
`G`-actions on sets `Y_n` differing from `X_n` by `o(|X_n|)` points.
For a finite generating set of `N`, every generator is asymptotically
trivial on `X_n`. The paper's Lemma 2.3 therefore removes only
`o(|X_n|)` points so that all of `N` fixes the remainder.

Now pass the genuine `G`-action on `Y_n` to the finite orbit set
`Y_n/N`. Normality makes this a genuine `Q`-action. The fixed remainder
embeds as singleton `N`-orbits, while the total number of orbit points is
still `(1+o(1))|X_n|`; the induced action agrees with `sigma_n` on all but
`o(|X_n|)` points. This is exactly a flexible correction of `sigma_n`.

The hypothesis is finite generation of `N` as a group, not merely finite
normal generation. The result is quotient-direction permanence for flexible
permutation stability; it asserts no converse and no analogue for arbitrary
kernels or other metrics.

Source status: arXiv preprint v1, submitted 2025-12-17. The theorem and proof
were checked from the primary text on 2026-08-31.
