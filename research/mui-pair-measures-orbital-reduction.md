---
rg: 2
id: mui-pair-measures-orbital-reduction
kind: claim
title: MUI Gamma-invariant pair measures have N-invariant marginals, and at Gamma-exact lifts (MUI-J) is exactly N-invariance of mixtures of Gamma-orbit measures on pairs
distinct_from:
  mui-commutant-reduces-to-internal-joining-invariance: that proves (MUI-C) iff (MUI-J) and kills the standard-part joining route; this proves that the one-point part of (MUI-J) (the marginals) is already a theorem, and that at Gamma-exact lifts the internal measures may be replaced by exactly Gamma-invariant orbital mixtures, leaving only their conditional (off-diagonal) structure open.
  hamming-enemies-escape-finite-hull-pair-loeb-scales: that handles pair measures dominated by G-invariant pair scales; this handles the marginals of arbitrary MUI measures, with no domination hypothesis, and reduces the rest to orbit combinatorics of an exact Gamma-action on Y x Y.
  kun-thom-nonsofic-wreath: Theorem 4.1 is the case of permutation-graph measures; the orbital mixtures here include every Hecke-type (double coset) coupling, which Theorem 4.1 does not cover.
artifacts:
  - research/mui-pair-measures-orbital-reduction-proof.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED (proposed; full proof in
`mui-pair-measures-orbital-reduction-proof`).** The proof uses Kun--Thom
Theorem C verbatim (`research/artifacts/kun-thom-2608-06222-verified.md`),
the Loeb construction, and property (T) of `Gamma` through a Kazhdan pair.
Nothing else is imported.

This is a wave step on `approximate-collapse-for-kt-compressor`, after
`mui-commutant-reduces-to-internal-joining-invariance`: attack (MUI-J)
directly.

## Setting

As in `mui-commutant-reduces-to-internal-joining-invariance`. `Gamma < G` is
infranormal, not normal, both Kazhdan (the Theorem E pair is the main case);
`N` is the normal closure of `Gamma`. `s_n : G -> Sym(Y_n)` is a lift of a
sofic representation `sigma`, `W_n = Y_n x Y_n`, `psi_n(g) = s_n(g) x s_n(g)`.
`lambda = (lambda_n)` is an internal pair measure (probability measures on
`W_n`), with marginals `mu^1_n, mu^2_n` of densities `f^i_n` relative to the
uniform measure `u_n` on `Y_n`.

The lift is **Gamma-exact** if `s_n` restricted to `Gamma` is a
homomorphism for `U`-almost every `n`.

## Theorem

**(1) Marginal collapse (every sofic sigma).** If `lambda` is MUI and
internally `Gamma`-invariant, then both marginals are internally
`N`-invariant: `||s_n(u)_* mu^i_n - mu^i_n||_TV -> 0` for every
`u in N`. Equivalently: the densities
`f^i = [f^i_n]` are internal functions whose uniformly integrable
truncations have `N`-fixed standard parts. This half of (MUI-J) is a
consequence of Kun--Thom Theorem C applied to the Loeb action; no pair
structure is needed.

**(2) Internal equivariance is automatic.** Every MUI internal pair measure
is internally equivariant. So the hypothesis list of (MUI-J) is just
"MUI + internally `Gamma`-invariant".

**(2') Finite form.** Fix a finite `T subset P_Gamma` with
`G = <Gamma, T>`. For every sofic `sigma`, (MUI-J) is equivalent to: for
every MUI internally `Gamma`-invariant `lambda` and every `t in T`, the push
`psi_n(t)_* lambda_n` is internally `Gamma`-invariant. (It is always
internally `Lambda_t = t Gamma t^-1`-invariant; the question is the upgrade
from `Lambda_t` to `Gamma`.)

**(3) Orbital reduction at Gamma-exact lifts.** Suppose the lift is
Gamma-exact. Call `nu = (nu_n)` **orbital** if each `nu_n` is exactly
`psi_n(Gamma)`-invariant, i.e. a convex combination of uniform measures
on `psi_n(Gamma)`-orbits of `W_n`. Then for every MUI internally
`Gamma`-invariant `lambda` there is an MUI orbital `nu` with
`||lambda_n - nu_n||_TV -> 0`. Hence, at such `sigma`,

```text
(MUI-J)  <=>  (MUI-O): every MUI orbital pair measure is internally
                       g^-1 gamma g-invariant for all g in G, gamma in S,
```

where `S` is a finite generating set of `Gamma`. (These conjugates generate
`N`, and internal invariance under finitely many elements passes to every
word in them, by (2).)

The orbits of `psi_n(Gamma)` on `W_n` are the Hecke data of the finite
`Gamma`-set `Y_n`: for orbits `Gamma a = Gamma/H` and `Gamma b = Gamma/H'`
(finite-index stabilizers), the pair orbits in `Gamma a x Gamma b` are the
double cosets `H \ Gamma / H'`. Permutation-graph measures (Theorem 4.1)
are the orbital measures supported on double cosets of size one on each
side, i.e. on equivariant bijections between isomorphic orbits.

**(4) The fully exact case is closed.** If moreover `s_n` is a homomorphism
on all of `G`, (MUI-O) holds (this is the argument of
`mui-commutant-reduces-to-internal-joining-invariance` (2a), which needs only
exactness): `s_n(N) = s_n(Gamma)` as permutation groups.

## What remains, exactly

After (1)--(3), the whole content of (MUI-J) at a Gamma-exact lift is the
off-diagonal part. By (2'), take an MUI orbital `nu` (a mixture of
`Gamma`-orbit measures on `Y_n x Y_n`, whose marginals are already
`N`-invariant by (1)) and `t in T`. The push `psi_n(t)_* nu` is internally
`Lambda_t`-invariant (the Hamming defects of `s_n(t)` cost `o(1)` mass by
MUI), and it must be shown internally `Gamma`-invariant. `psi_n(t)` maps
the `Gamma`-orbital partition of `W_n` to an (approximately)
`Lambda_t`-orbital partition, and `Lambda_t`-orbits refine `Gamma`-orbits.
So (MUI-O) is the pair-orbit analogue of the counting collapse in
Kun--Thom's Proposition 3.1: this refinement must be trivial on
`nu`-mass. The one-point version of the collapse is (1). The obstruction to
running the same count on pairs is that pair orbits need not be large: a
single orbit may carry `nu`-mass on a set of `u_n x u_n`-density
`O(1/|Y_n|)`, so Kun's expander decomposition of `W_n` for the uniform
measure does not see `nu`.

## Next step

Prove (MUI-O) by a weighted expander decomposition of the orbital measure:
decompose `(W_n, nu_n)` by the `Lambda`-orbits inside each `Gamma`-orbit and
show, using that `psi_n(t)` is a bijection of `W_n` that preserves the
multiset of orbit sizes of `psi_n(Gamma)` versus `psi_n(Lambda)` up to
`o(1)` mass, that the `nu`-weighted size distribution forces the refinement
to be trivial. Or refute it by an exact-Gamma lift with a double coset
`H g H'` whose `psi_n(t)`-image is a different double coset of the same
size.
