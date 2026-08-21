---
rg: 2
id: affine-leavitt-boundary-shear-payment
kind: claim
title: Paired Steinberg shears charge the full binary boundary of the affine active window
artifacts:
  - research/artifacts/affine-leavitt-normalized-hs-decoder-audit-2026-08-21.md
distinct_from:
  affine-leavitt-steinberg-hs-coefficient-decoder: that asks for four contractions with one modulus valid for every sufficiently accurate representation; this asks only for depth-dependent scalar mark estimates on canonical-trace microstates.
  steinberg-root-shear-plancherel-covariance: that gives full stationary transport on one invariant finite root window; this must retain the non-invariant boundary and charge it through paired multiplication triangles.
  relative-leavitt-active-subspaces-expand-by-two: that proves the coefficient boundary has full algebraic size; this is the missing normalized-HS conversion of that boundary into marked-root energy.
---

OPEN.  For the fixed marked group

```text
Gamma_A=St_5(L_A(k[C_aff])),             w_A=x_12(A),     (BSP1)
```

construct, for every depth `N`, a finite coefficient/root window `F_N` and a
finite constant `C_N` such that every unitary tuple on the fixed presentation
satisfies

```text
||w_A(U)-I||_2^2
 <= 2^-N+C_N(def(U)+sep_(F_N)(U)).                       (BSP2)
```

Here `sep_(F_N)` is the canonical-delta trace error on the finitely many
nonidentity words in the window.  Constants may grow arbitrarily with `N`.

The intended construction uses a nested sequence `V_0 subset V_1 subset ...`
of finite active coefficient spaces.  At each completed binary step,
`relative-leavitt-active-subspaces-expand-by-two` gives

```text
dim(s_0V_n+s_1V_n)=2 dim(V_n).                            (BSP3)
```

For every multiplication appearing in that step,
`steinberg-root-shear-plancherel-covariance` exposes
the corresponding row-root action as an almost permutation of Plancherel
Fourier blocks.  The missing estimate is a paired-triangle boundary lemma:
the two diagonal identities `t_i s_i=A`, the two cross-zero identities, and
the range-sum identity must force either

1. a disjoint-range/Gram payment on the Fourier blocks which remain in the
   old window; or
2. an HS payment at least equal to the mass which exits into
   `V_(n+1)\V_n`.

Iterating that one-step inequality would leave at most `2^-N` uncharged
active mass and prove `(BSP2)`.  Merely closing each window and treating all
shears as full permutations cannot work, by
`plancherel-root-shears-have-no-compression-pressure`; the boundary must stay
visible until it is paid.  Nor can one assign successive prefix boundaries
to first-detection layers of a single additive root coordinate:
`leavitt-prefix-boundaries-do-not-split-additive-character-mass` constructs
one character which detects all of them.  The payment must therefore be a
paired-coordinate Gram/range estimate, not a scalar character count.

The exact paired-coordinate supply is already present:
`leavitt-prefixes-form-exponential-heisenberg-packet` produces `2^n`
independent Weyl partners at depth `n`.  However,
`affine-leavitt-profile-computable-checkpoints` shows what follows from that
packet without the boundary lemma: only a computable sequence of rapidly
shrinking error checkpoints forcing rapidly growing matrix dimension.
Hyperlinearity permits that growth.  Thus the missing one-step estimate must
convert the same Weyl packet into loss of normalized marked mass, not merely
into a lower bound on the ambient dimension.

By `fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity`, `(BSP2)`
would prove the explicit group `(BSP1)` nonhyperlinear without the stronger
all-representations decoder `(ALD1)--(ALD2)`.

## Attempts

- **Closing one finite root window loses the signal.**  If every named
  multiplication is completed to an automorphism of one finite additive
  root group, Fourier transform turns it into a permutation of equal-density
  Plancherel atoms.  Their uniform vector is stationary by
  `plancherel-root-shears-have-no-compression-pressure`, so no scalar decay
  follows.
- **The depth-`N` Heisenberg packet gives dimension, not density.**
  `leavitt-prefixes-form-exponential-heisenberg-packet` forces a marked
  finite-dimensional sector to have dimension divisible by `p^(2^N)`, but
  that sector may still occupy all of an arbitrarily large matrix model.
  Thus packet rank alone cannot prove `(BSP2)`.
- **Additive first-detection does not split the boundary.**
  `leavitt-prefix-boundaries-do-not-split-additive-character-mass` constructs
  one additive character which is nontrivial on every binary prefix at every
  depth.  Counting new coefficient directions therefore does not create
  disjoint spectral carrier mass by itself.
- **The remaining live attack keeps the boundary unclosed.**  Use separate
  source and target root windows for left multiplication by `s_0,s_1` and
  return maps `t_0,t_1`.  The paired Steinberg triangles must then show that
  mass leaving the old window is either placed in two orthogonal target
  families or paid by a word defect.  No such quantitative Gram/boundary
  lemma has yet been proved; it is the exact open content of this claim.
- **Square return itself is no longer a gate.**  If the boundary argument
  first closes source and target on the same finite paired reservoir, then
  `bistochastic-diagonal-return-forces-aligned-permutation` converts each
  near-identity diagonal forward/return composition to an aligned
  permutation/inverse pair with constants `2` and `5`, independent of the
  label count.  The robust paired `1/36` floor then consumes the crossed-zero
  relation.  Hence the unresolved estimate is only the same-reservoir
  boundary payment that excludes `rectangular-escape`.
- **A closed multilevel return has no depth loss.**  Once the same physical
  reservoir is identified at the end of a binary depth-`N` cycle,
  `closed-multiplicity-cycle-kills-carrier-trace` gives
  `tr(P_0) <= 3 epsilon + return_error/(2^N-1)`.  Thus the desired contractive
  recurrence does not need to be proved cell by cell with separately tracked
  constants.  The only missing estimate is the matrix-coordinate assertion
  that boundary mass cannot pay for label doubling by shrinking multiplicity
  before the return.
