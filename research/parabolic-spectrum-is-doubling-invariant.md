---
rg: 2
id: parabolic-spectrum-is-doubling-invariant
kind: claim
title: In any approximate representation of SL2(Z[1/2]) the parabolic spectrum is approximately invariant under z to the fourth
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-question-as-square-root-of-parabolic: that is the amalgam/square-root presentation; this is a spectral constraint on the parabolic coming from a single hyperbolic element of the S-arithmetic group, and it turns the far sector into a transfer-operator statement.
  sl2-s-arithmetic-pair-is-codense-kazhdan: that uses the same conjugation to prove finite order in EXACT representations; this is the quantitative approximate version and its measure-theoretic consequence.
---

The element `h = diag(2, 1/2)` lies in `SL_2(Z[1/2])` and satisfies, with the
parabolic `U = [[1,1],[0,1]]`,

```text
h U h^(-1) = U^4.                                                       (DI1)
```

**Exact form.**  In any finite-dimensional unitary representation `rho`,
`rho(U)` is conjugate to `rho(U)^4`, so its spectrum is invariant under
`z -> z^4`.  A finite `z -> z^4`-invariant subset of the unit circle is a
union of orbits, each a set of roots of unity of odd order (the map is a
bijection of `mu_n` iff `n` is odd).  Hence `rho(U)` has odd finite order,
which is the congruence subgroup property seen through one element, and the
source of `sl2-s-arithmetic-pair-is-codense-kazhdan`.

**Approximate form.**  Let `(pi_n)` be an asymptotic representation with
`Def(pi_n) -> 0`, and let `mu_n` be the spectral distribution of `pi_n(U)`
(the empirical measure of its eigenvalues, a probability measure on the
circle).  Since `h` is a fixed word in the generators, `(DI1)` holds up to
`O(Def)`, so

```text
W_1( mu_n , (z -> z^4)_* mu_n ) -> 0,                                   (DI2)
```

the pushforward under the fourth-power map is asymptotically fixed
(`W_1` = Wasserstein; equivalently every Fourier coefficient satisfies
`hat mu_n(k) - hat mu_n(4k) -> 0`).

**Consequence: the far sector is a transfer-operator problem.**  A
congruence representation has `mu_n` supported on odd roots of unity (the
`z -> z^4`-periodic points).  A far-sector counterexample to
`iwahori-local-global-defect-question` would need `mu_n` bounded away from
every such atomic measure while `(DI2)` holds.  The `z -> z^4`-invariant
measures are exactly the fixed points of the Ruelle transfer operator; they
include Lebesgue (whose parabolic is the bilateral shift, i.e. the tempered
principal-series / regular direction) and a large family of Gibbs measures on
Cantor sets.  So the spectral constraint alone does NOT force atomic
spectrum, and the far sector cannot be closed by the parabolic alone: the
remaining rigidity must couple `U` to its opposite `L = S U S^(-1)` and to
their half-powers.

## Attempts

- **What (DI2) rules out.**  Any accumulation measure `mu` of `(mu_n)` is
  exactly `z -> z^4`-invariant.  If additionally the opposite parabolic
  `L` has spectral measure `nu` with `nu = (z -> z^4)_* nu` (same argument
  with `h^(-1)`), and the representation forces `mu` and `nu` to be related
  by the `S`-conjugation `L = S U S^(-1)` (so `nu = mu`) and by the
  half-parabolic square roots, the joint constraint is much stronger than
  either alone.
- **BS(1,4) subgroup.**  `<U, h> = BS(1,4)`, amenable, hence hyperlinear;
  its HS-stability (open in general for Baumslag--Solitar groups) is
  exactly the question whether `(DI2)` forces `mu_n` near a `z -> z^4`-
  invariant measure with an explicit modulus.  Ambient stability of
  `SL_2(Z[1/2])` neither follows from nor implies BS(1,4)-stability, but a
  quantitative transfer-operator bound for `BS(1,4)` is a concrete
  sub-target.
- **Why Lebesgue is not a counterexample by itself.**  The regular
  representation of `SL_2(Z[1/2])` has parabolic spectrum Lebesgue and IS
  approximable (the group is sofic/hyperlinear), but its finite models are
  the quasi-regular/congruence ones whose `mu_n` are atomic and converge
  weakly to Lebesgue; so `mu_n -> Lebesgue` is compatible with each `mu_n`
  atomic (congruence).  The far sector needs `mu_n` FAR from atomic at
  finite `n`, which weak convergence does not provide.  This is the exact
  gap the numerical probe `experiments/psl2_far_sector_probe.py` targets.
