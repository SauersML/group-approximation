---
rg: 2
id: marked-approximate-radical-survives-solution-group-embedding
kind: claim
title: A marked approximate-radical witness survives Slofstra's fixed-word embedding into a solution group
distinct_from:
  slofstra-solution-group-embedding-preserves-marked-involutions: that is the exact group-theoretic embedding theorem; this adds the elementary normalized-HS restriction argument and consumes an approximate-radical hypothesis already present in the input group.
  perfect-lcs-gap-implies-nonhyperlinear: that obtains the radical property of the solution-group sign from a strict finite-dimensional game-value gap; this transfers a radical property already proved for the embedded source word.
  slofstra-involution-not-sofic-radical: that refutes the radical hypothesis for the particular Higman-based sign in the older Tsirelson-separation construction; this is the conditional transfer theorem explaining what stronger source would have sufficed.
  wagon-wheel-exact-radical-has-hs-wall: that combines exact finite-dimensional invisibility and separated permutation microstates for the actual motivating output; this is the positive transfer theorem under the strictly stronger source-modulus hypothesis.
---

**ESTABLISHED.**  Let `G` be finitely presented, let `J' in Z(G)` be a
nontrivial involution, and suppose `J'` is trivial in every normalized-HS
asymptotic representation of `G`.  Apply
`slofstra-solution-group-embedding-preserves-marked-involutions` to obtain

```text
phi:G -> Gamma,              phi(J')=J.
```

Then `J` is nontrivial in `Gamma` and trivial in every normalized-HS
asymptotic representation of `Gamma`.  Hence the finitely presented solution
group `Gamma` is nonhyperlinear.

This transfer is dimension-free and quantitative.  For fixed finite
presentations there are effectively computable constants `A,B<infinity`
such that, if

```text
kappa_G(epsilon)=sup { ||sigma(J')-1||_2 : Def_G(sigma)<=epsilon },
```

then the solution-group sign obeys

```text
kappa_Gamma(delta) <= kappa_G(A delta)+B delta.             (MAR1)
```

The constants come from the explicit van Kampen pictures for the substituted
source relators and the marked equality.  In the wagon-wheel picture
presentation, a collegial relator of length `l` has the displayed filling
with `3l` vertices, so these constants are computed directly from the finite
construction.  No stability or quantitative constellation theorem is needed:
the decoder is restriction along fixed embedding words, not perturbation of
the whole output tuple to an exact solution-group representation.

Proof: `fixed-word-restriction-transfers-approximate-radical-proof`.

This is a compiler, not a source of the missing witness.  Exact
finite-dimensional invisibility of `J'` is insufficient; the hypothesis
quantifies over approximate representations.

The hypothesis is sharp even within the wagon-wheel construction.
`wagon-wheel-exact-radical-has-hs-wall` gives the explicit motivating solution
group whose sign is killed by every exact finite-dimensional representation
but remains at normalized-HS distance `sqrt(2)` in asymptotic permutation
models with arbitrarily small relator defect. Thus `(MAR1)` cannot be fed only
the exact statement `kappa_G(0)=0`; it needs control of `kappa_G(epsilon)` as
`epsilon->0` across unbounded dimensions.
