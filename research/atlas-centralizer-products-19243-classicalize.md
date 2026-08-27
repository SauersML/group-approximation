---
rg: 2
id: atlas-centralizer-products-19243-classicalize
kind: claim
title: The thirty shifted A4 centralizer products plus collision 19243 force a classical chart branch
distinct_from:
  atlas-thirty-centralizer-products-classicalize: that packet-only target is refuted by 202 exact GL5(F2) models; this corrected target includes the interior collision which kills every one of those models.
  atlas-a4-root-energy-ellipse-ceiling: that asks only for one scalar energy inequality; this asks for the stronger geometric conclusion that the whole relative frame approaches a classical chart alignment modulo gauge.
artifacts:
  - experiments/atlas_a4_reference_alignment.py
  - experiments/atlas_a4_gl5_packet_screen.py
---

Fix `rho_k=Reg(A8) tensor I_k` and the exact packet reference alignment
`R_k=rho_k(r_0)` from `atlas-a4-packet-centralizer-product-compiler`.  For the
thirty packet contexts let `D_(j,k)` be the corresponding corrected shifted
double-centralizer sets

```text
C(rho_k(a_j)) R_k C(rho_k(b_j))
```

or the factor-reversed versions.  Let `q_19243(U)` denote the collision word.

Let `N_k` be the global regular-chart commutant

```text
N_k = U(rho_k(A8)').
```

For each of the sixty inner/outer classical packet alignments choose one
regular-chart implementing unitary `T_alpha`, and put

```text
B_k = union_alpha T_alpha N_k.
```

The right factor `N_k` is essential: `U` and `U C`, `C in N_k`, represent the
same second chart, so a finite set of literal unitary points cannot be the
correct gauge-invariant target.

**Claim.**  For every sequence `k_n` and every relative unitary sequence
`U_n in U(20160 k_n)`,

```text
max_j dist_2(U_n,D_(j,k_n)) -> 0
and
||q_19243(U_n)-1||_2 -> 0
```

imply

```text
dist_2(U_n,B_(k_n)) -> 0.                            (A4+Q-CLASS)
```

The modulus must be independent of the external multiplicity.

## Why this is the corrected joint target

- Packet-only classicalization is false: `atlas-a4-gl5-packet-collision-screen`
  gives 202 exact regular-margin packet models in `GL5(F2)`, including 172
  non-normalizer relative positions.  Collision 19243 is nonidentity on all
  202, so none refutes `(A4+Q-CLASS)`.
- The corrected reference alignment is structural, not cosmetic.  Without the
  shift `R_k`, several raw same-chart packet pairs have product order `6` or
  `2`, so the local A4 centralizer-product theorem is being applied to the
  wrong pair.
- `atlas-a4-aligned-component-generation-ladder` shows that after this shift
  the large `S3 x C3` packet component and its aligned conjugate have trivial
  intersection and generate all `A8`; the small component closes only to the
  rank-three `GL3(2)` core.  Thus a component-coherence proof should focus on
  the large `K_(2,4)` biclique and use collision as the missing cross-component
  / parabolic anchor.
- After canonical A4 qutrit normalization and biclique tree gauges,
  `atlas-a4-packet-four-rectangle-normal-form` leaves only four `U(k)`
  rectangle holonomies.  Therefore `(A4+Q-CLASS)` is equivalent to a fixed
  finite noncommutative holonomy-rigidity problem; the ambient dimension
  `20160 k` is not the true number of variables.

## Concrete attacks

1. **Rank-three completion first.**  In the exact reference geometry, a raw
   `S3` together with one aligned central `C3` has two overlapping regular-A4
   cells and generates `GL3(2)` of order `168`.  Compile those two cells to a
   finite rank-three representation, then use the remaining central `C3`
   direction to leave the affine parabolic.
2. **Collision as the missing transvection.**  The repeated first-chart letter
   in 19243 is exactly `t_23`; the packet already contains the `C3` on the
   23-edge.  Thus collision attempts to upgrade that `C3` to the missing
   `S3(23)`, matching the parabolic ladder
   `GL3(2) < AGL3(2) < A8`.
3. **Four-holonomy polynomial.**  Rewrite the S3-relative normal form of 19243
   after the two biclique tree gauges.  If its qutrit factors telescope, the
   residual is a fixed matrix-valued Laurent polynomial in the four rectangle
   holonomies.  Prove its zero set is exactly the sixty classical branch
   cosets modulo `N_k`, uniformly over finite coefficient algebras.
4. **Finite-rank screens as falsification, not proof.**  The exhaustive GL5
   screen is the complete first-rank test and has no packet+collision survivor.
   Extend to structured parabolic/linear overmodels only to search for an exact
   counterexample to `(A4+Q-CLASS)`; absence in finitely many groups is not a
   proof.
