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
trivial on `X_n`.

Here is the invariant-set detail needed at that point. The support in the
genuine `Y_n`-action of each kernel generator is `o(|Y_n|)`: inside
`X_n` this follows from closeness to the pulled-back action, and outside
`X_n` there are only `o(|X_n|)` points. Apply Lemma 2.3 on the genuine
`N`-set `Y_n`, not on the possibly non-invariant set `X_n`. It produces
a subset `Z_n subseteq Y_n`, fixed pointwise by all of `N`, with
`|Y_n \ Z_n|=o(|Y_n|)`. Thus `Z_n intersect X_n` is conull in `X_n`.

Pass the genuine `G`-action on `Y_n` to its finite set `O_n=Y_n/N` of
`N`-orbits. Normality makes this a genuine `Q`-action. Every point of
`Z_n intersect X_n` gives a distinct singleton orbit, and

```text
|X_n| - o(|X_n|) <= |O_n| <= |Y_n| = |X_n| + o(|X_n|).
```

If `|O_n|<|X_n|`, adjoin `|X_n|-|O_n|` trivial `Q`-orbits. Relabel the
resulting set as a superset of `X_n`, extending the canonical identification
of `Z_n intersect X_n` with its singleton orbits. This adds at most
`o(|X_n|)` points. For each fixed `q in Q`, outside an `o(|X_n|)`
exceptional set both `x` and `sigma_n(q)x` lie in the fixed remainder and
the original correction agrees with the pullback, so the relabelled genuine
`Q`-action agrees with `sigma_n(q)`. It is the required flexible
correction.

This formulation also corrects two wording slips in the preprint: Lemma 2.3
must be applied on `Y_n`, and a singleton `N`-orbit means that `N` fixes
the point, so its `N`-stabilizer is all of `N`, not trivial.

The hypothesis is finite generation of `N` as a group, not merely finite
normal generation. The result is quotient-direction permanence for flexible
permutation stability; it asserts no converse and no analogue for arbitrary
kernels or other metrics.

Source status: arXiv preprint v1, submitted 2025-12-17. The theorem and proof,
including the invariant-set and relabelling repairs above, were checked
2026-08-31.
