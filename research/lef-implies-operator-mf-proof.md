---
rg: 2
id: lef-implies-operator-mf-proof
kind: route
title: Run the locally-finite MF argument on local embeddings
target: lef-implies-operator-mf
requires: [countable-group-mf-conventions]
artifacts: [non_mf_groups_exist.tex, GroupApproximation/Sofic/LocallyFiniteMF.lean]
---

## Direct proof

Let `G` be countable and LEF, and let `F_1 <= F_2 <= ...` exhaust `G` by
finite subsets.  For each `n` choose a finite group `Q_n` and a map
`phi_n : F_n F_n -> Q_n` that is injective on `F_n F_n` and satisfies
`phi_n(gh) = phi_n(g)phi_n(h)` whenever `g, h, gh` lie in `F_n` — that is the
definition of local embeddability.

At coordinate `n` represent `g in F_n` by the permutation matrix of left
translation by `phi_n(g)` on `Q_n`, and by the identity for `g` outside `F_n`.
For `g, h in F_n` the product is represented exactly, so the induced map into
the norm matrix corona is a homomorphism.  For `g != 1`, once `g in F_n` the
element `phi_n(g)` is nontrivial, so left translation by it is a
fixed-point-free permutation of `Q_n`; a fixed-point-free permutation matrix
has an eigenvalue at angle at least `2 pi / 3` from `1`, giving operator-norm
distance at least `sqrt 3` from the identity.  Hence the corona map is
injective and `G` is operator MF.  This is verbatim the argument of `lem:lfmf`,
which is the special case where `Q_n` may be taken to be a finite *subgroup*;
`countable-group-mf-conventions` transports the conclusion to every equivalent
formulation.
