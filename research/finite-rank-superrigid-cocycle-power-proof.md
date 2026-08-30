---
rg: 2
id: finite-rank-superrigid-cocycle-power-proof
kind: route
title: Detect a nonzero fixed-point coefficient among the first n powers
target: finite-rank-superrigid-cocycles-cannot-cancel-fixed-points
requires: []
---

Choose a measurable `q:X->U(n)` such that, with the cocycle convention
`b_(gh)(x)=b_g(x)b_h(g^(-1)x)`,

```text
b_g(x)=q(x) pi(g) q(g^(-1)x)^*.                        (SRP1)
```

On `Fix(g)`, the two values of `q` coincide. Conjugacy invariance of
normalized matrix trace therefore gives

```text
tr_n(b_g(x))=tr_n(pi(g)).                               (SRP2)
```

The relation-algebra fixed-point expectation formula factorizes as

```text
(tr_n tensor tau_R)(v_g)
 =mu(Fix(g)) tr_n(pi(g)).                               (SRP3)
```

Because the action is not essentially free and `Gamma` is countable,
choose `g!=e` with `mu(Fix(g))>0`. Torsion-freeness makes every `g^k`,
`k>=1`, nonidentity, and

```text
Fix(g) subseteq Fix(g^k),
mu(Fix(g^k))>0.                                        (SRP4)
```

Put `U=pi(g)` and let its eigenvalues be
`lambda_1,...,lambda_n`. Some power sum among the first `n` is nonzero:

```text
sum_i lambda_i^k !=0       for some 1<=k<=n.            (SRP5)
```

Indeed, if the first `n` power sums all vanished, Newton's identities would
successively force every elementary symmetric polynomial in the
`lambda_i` to vanish, including their product `det(U)`. This contradicts
unitarity. Combining `(SRP3)--(SRP5)` proves `(SRC2)`.

The hypotheses are sharp. For the trivial action of `Z` on `(T,Haar)`,
the scalar cocycle `b_k(z)=z^k` cancels every nonzero power, but it is not
cohomologous to a constant homomorphism: for a trivial action a scalar
coboundary is trivial, while `z^k` varies diffusely.

For the coinduction application, Drimbe's Theorem A in
`arXiv:1512.00093` states that, under its relative-property-`(T)` and
w-normality hypotheses, every cocycle for the coinduced action with values
in a `U_fin` group is cohomologous to a homomorphism. Since `U(n)` is
such a target, `(SRC2)` applies whenever the actor is torsion-free and the
coinduced action retains nontrivial isotropy.
