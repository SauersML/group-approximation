---
rg: 2
id: hecke-far-commutator-defect-formula
kind: claim
title: The far Hecke commutator defect of a subgroup-central unitary is an exact scalar
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that asserts the collapse; this is an unconditional identity, valid in both the collapse and the counterexample scenario, which compresses the entire far sector into one scalar per element.
  hnn-route-is-relative-commutant-collapse: that identifies the HNN route with the collapse problem; this computes the exact asymptotic value of the commutator defect along the double-coset filter for every finite tracial algebra.
  sl3-pair-relative-commutant-route: that selects the higher-rank pair for its spectral gap; this holds for every Hecke pair with a Howe-Moore Schlichting completion, of any rank.
---

Let `(Gamma, Lambda)` be a Hecke pair whose Schlichting completion `G`
is, modulo a finite kernel, a simple algebraic group over a local field
with the Howe--Moore property, and let `K <= G` be the compact open
closure of `Lambda`.  The instances used downstream are

```text
Gamma = SL_n(Z[1/p]),  Lambda = SL_n(Z),  G = PSL_n(Q_p),  n >= 2,
```

with `G` the Schlichting completion by Shalom--Willis/Tzanev.  Let `M` be
ANY von Neumann algebra with faithful normal trace `tau`, let
`pi : Gamma -> U(M)` be any unitary representation, and let `k` be a
unitary in `pi(Lambda)' cap M`.  Set

```text
psi_k(g) = tau(k* pi(g) k pi(g)*).                       (HFD1)
```

Then:

1. `psi_k` is positive definite on `Gamma`, `Lambda`-bi-invariant, and
   `psi_k = 1` on `Lambda`; it extends to a `K`-bi-invariant positive
   definite function on `G`.
2. The commutator defect is its real part exactly:

   ```text
   || k pi(g) - pi(g) k ||_2^2 = 2 - 2 Re psi_k(g).      (HFD2)
   ```

3. Along the cofinite filter of double cosets `Lambda gamma Lambda`
   (equivalently `gamma -> infinity` in `G`),

   ```text
   lim psi_k(gamma) = || E(k) ||_2^2,                     (HFD3)
   lim || [k, pi(gamma)] ||_2^2 = 2 (1 - || E(k) ||_2^2), (HFD4)
   ```

   where `E` is the trace-preserving conditional expectation of `M`
   onto the full relative commutant `pi(Gamma)' cap M`.

Consequences.  Either `k` lies in `pi(Gamma)' cap M`, or its commutator
defect is uniformly bounded below outside finitely many double cosets;
and `tau`-orthogonality to `pi(Gamma)' cap M` forces the maximal
asymptotic defect `2`: far Hecke conjugates of such a `k` become
orthogonal to `k`.  For the pairs above this replaces the unstructured
"far sector" of the relative-commutant program by one scalar
`s = ||E(k)||_2^2` per element, and `(RCC)` becomes the single
assertion `s = 1` for every unitary of `pi(Lambda)' cap M` in a matrix
ultraproduct.  The enemy scenario is precisely a spherical positive
definite function `psi = s + (1-s) phi` with `phi` a `c_0` spherical
coefficient of `G`; in the quasi-regular case (`psi = 1` on `Lambda`,
`0` far away in the limit) the decay of `phi` follows the
Harish-Chandra `Xi`-profile of `L^2(G/K)`.
