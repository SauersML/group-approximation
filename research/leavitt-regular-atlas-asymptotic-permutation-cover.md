---
rg: 2
id: leavitt-regular-atlas-asymptotic-permutation-cover
kind: claim
title: Build asymptotic finite covers of the universal Leavitt atlas with free regular A8 vertex actions
refuted_by: leavitt-regular-atlas-permutation-cover-impossible
distinct_from:
  leavitt-regular-atlas-hyperlinearity-criterion: that permits an arbitrary relative unitary and is equivalent to hyperlinearity of Q; this asks for the stronger permutation-unitary witness, which would make a central extension of Q sofic.
  atlas-a8-mixed-block-transport-has-permutation-models: that realizes every rational one-step mixed-block marginal by a permutation; this asks that the same permutation close every fixed multi-step atlas relator loop on almost every sheet.
  finite-sheet-transport-networks-are-exactly-matricial: that retains arbitrary cycle holonomy in an exact monomial model; this asks that the particular universal-central-extension holonomies be asymptotically trivial.
  openai-leavitt-unit-nonsofic: that excludes soficity of Q itself; this asks for a sofic central extension of Q, and soficity is not known to descend through arbitrary central quotients.
---

**REFUTED finite combinatorial target.**  Use the canonical source and normal
generators of `leavitt-regular-atlas-hyperlinearity-criterion`:

```text
bar P = K_1 * K_2 = A_8 * A_8,
bar N = <<bar S>>_(bar P),
U_Q = bar P/bar N.
```

Construct finite sets `Omega_n`, with `|Omega_n|=20160 k_n`, and two actions

```text
alpha_n,beta_n:A_8 -> Sym(Omega_n)                       (APC1)
```

such that:

1. each action in `(APC1)` is free, equivalently is `k_n` copies of the
   left regular `A_8`-set;
2. for the homomorphism

   ```text
   rho_n:A_8*A_8 -> Sym(Omega_n)
   ```

   determined by `alpha_n,beta_n`, every fixed normal generator closes on
   almost every sheet:

   ```text
   max_(s in bar S) d_H(rho_n(s),1) -> 0.                (APC2)
   ```

After identifying both free `A_8`-sets with `A_8 x [k_n]`, the second
identification differs from the first by one permutation `U_n`.  Thus
`(APC1)--(APC2)` are exactly the permutation-unitary specialization of the
regular-atlas criterion.

Equivalently, form the finite complex-of-groups presentation with vertex
groups `A_8,A_8` and 2-cells labelled by `bar S`.  The target is a sequence
of finite almost-covers whose local vertex-group actions are honest regular
covers and for which the union of the failed 2-cell lifts has density
`o(1)`.  No separation condition beyond `(APC1)` is needed.

## What the rational absorber does and does not supply

The mixed-block transportation table of a permutation `U_n` records only its
one-step pair marginals.  `atlas-a8-mixed-block-transport-has-permutation-models`
proves that every rational table with the regular margins is attainable, so
there is no local rank, denominator, or Hall obstruction to `(APC1)`.

Condition `(APC2)` is strictly joint: if

```text
s=g_1 h_1 ... g_l h_l,
```

its defect is the fraction of sheets whose entire alternating trajectory
under the two actions fails to return.  Pair marginals do not determine this
`l`-step return statistic.  Gluing the rational absorbers therefore means
choosing one common sheet permutation whose finitely many prescribed return
maps all have `o(1)` support.  Retaining arbitrary return permutations, as in
the finite-sheet transport theorem, gives exact matrices but not `(APC2)`.

This formerly looked like the smallest positive construction, but
`leavitt-regular-atlas-permutation-cover-impossible` now rules it out. The
reason is special to the Leavitt target: every nontrivial permutation
ultraproduct image would be a sofic central extension of `Q`, whereas every
countable central extension of `Q` is nonsofic.

## Attempts

- **Glue rational mixed-block absorbers.**  This settles every one-step
  transportation margin but leaves the joint word trajectories unspecified.
  Choosing the absorbers independently for different relators does not give
  one permutation `U_n`; choosing one permutation retains its actual cycle
  holonomies, which need not satisfy `(APC2)`.  The missing operation is a
  simultaneous coupling of all finitely many path-return statistics. The
  all-central-cover obstruction proves that no such permutation coupling
  exists.
- **Use exact finite covers.**  This is impossible.  If every element of
  `bar S` were identically trivial on one finite cover while a factor acted
  freely, it would give a nontrivial finite quotient of the quasisimple
  universal central extension `U_Q`.  A perfect central extension of the
  infinite simple group `Q` has no nontrivial finite quotient.  Thus any
  successful sequence must retain a nonempty defect set at every finite
  stage and make only its density vanish; residual finiteness cannot supply
  the construction.
- **Take a random relative permutation.**  Independent regular charts have
  no reason for the fixed alternating relator loops to close; generic word
  maps move macroscopic mass.  Randomness may still be useful only after a
  correlated lift/repair scheme has imposed the central return laws.  No such
  repair is presently known, so the construction is deferred at this joint
  return-coupling step.
