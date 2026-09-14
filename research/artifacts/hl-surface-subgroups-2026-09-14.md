# Lane hl-surface-subgroups: surface subgroups in the hyperbolic KMS groups (2026-09-14)

Target: Gromov's surface subgroup question (`one-ended-hyperbolic-groups-contain-surface-subgroups`).

## Result

For every odd prime `p`, four of the six hyperbolic Kac–Moody–Steinberg families of Caprace–Conder–Kaluba–Witzel
contain quasiconvex genus-2 surface subgroups: `G_HB2(2)(p)`, `G_HC2(2)(p)`, `G_HB2(3)(p)` and `G_HBC2(3)(p)`.
- By CCKW Corollary 7.8, they have property (T) for `p ≥ 7` (`(3,4,4)` types) or `p ≥ 11` (`(4,4,4)` types).
- So Gromov's question has a positive answer for infinitely many pairwise non-isomorphic hyperbolic Kazhdan
  groups. These groups are rigid (they have no splittings), which is exactly the case left open by Wilton's
  reduction.

Landed:
- `cckw-kms-triangle-groups-structure` and its `-citation` route: CCKW Theorem 3.1, the six non-euclidean KMS
  presentations, Proposition 7.6, Theorem 7.7 and Corollary 7.8.
- `kms-hb2-girth-surfaces-give-surface-subgroups` and its `-proof` route: the criterion for `G_HB2(2)(p)`, with
  vertex-group intersections from a symbolic quotient to `SL_4(F_p)`.
- `kms-girth-surfaces-give-surface-subgroups` and its `-proof` route: the criterion for all six families.
  Intersections come from counting at a vertex, and vertex orders from semidirect products.
- `kms-hb2-groups-contain-genus-two-surface-subgroups` and its `-proof` route: one 24-chamber integer-labelled
  surface, labels `−1, 1, 2`.
- `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups` and its `-proof` route: certificates from MSI job 785007.
- `experiments/kms-hb2-surface-subgroups/`:
  - search code, with vertex words evaluated through the normal-form laws;
  - two independent verifiers: normal-form laws in `verify_integer_certificate.py`, integer matrix models in
    `verify_kms_certificates.py`;
  - girth checks, calibration logs and search outputs.
- Item 7 of the covered classes in the root node.

## How it was found

The `F_7` certificates of `ghb7-contains-a-genus-two-surface-subgroup` (lane ideas-growth-hyperbolic) list six
labelled girth surfaces. Lift each label from `{1, …, 6}` to `{−3, …, 3}` and evaluate the 72 vertex words over
`Z`. Nontrivial words per surface:

| surface | 25 | 29 | 31 | 43 | 65 | 67 |
|---|---|---|---|---|---|---|
| nontrivial words | 56 | 64 | 64 | 32 | 12 | **0** |

On surface 67 every vertex word is trivial in the integral nilpotent groups `N_3`, `N_4`. These surject onto
`U_3(p)`, `U_4(p)` for every `p`, and no label is divisible by an odd prime, so one surface works at every odd
prime.

The search then solved directly over `Z`, with labels in `{±1, ±2}`, on all girth surfaces of the smallest
orientable sizes (MSI job 785007, `summary-job785007.txt`):

| family | type | T | girth surfaces | surfaces with a labelling |
|---|---|---|---|---|
| `G_HB2(2)` | `(3,4,4)` | 24 | 72 | 1 (surface 67) |
| `G_HC2(2)` | `(3,4,4)` | 24 | 72 | 1 (surface 67) |
| `G_HBC2(2)` | `(3,4,4)` | 24 | 72 | 0 |
| `G_HC2(1)` | `(3,3,4)` | 24 | 5 (all non-orientable) | 0 |
| `G_HB2(3)` | `(4,4,4)` | 16 | 61 | 1 (surface 29) |
| `G_HBC2(3)` | `(4,4,4)` | 16 | 61 | 2 (surfaces 18, 28) |

At `T = 8`, the four `(4,4,4)` girth surfaces have no labelling even with labels in `{±1, ±2, ±3}`.

## What had to be proved for general `p` and general families

For every odd `p` and all six families, the criterion proof shows:
- vertex orders `p^3`, `p^4` via `(Z/p)^r ⋊ Z/p` (with `φ^p = id` because `p | C(p,2)`);
- link girths `6, 8, 8`, via the normal-form law: no 4-cycles, and for `U_4` no 6-cycles, by the integer
  identity `2ν + e_3f_2f_3 = −(1+f_1)μ`;
- edge stabilizers of order `p` by counting the bipartite link. So `X_i ∩ X_j = <g_k>` and the chamber
  stabilizer is trivial.

The rest follows the `p = 7` proof. That includes the quasiconvexity argument tightened in 31d5884ac: Švarc–Milnor,
stability of quasi-geodesics, and hyperbolicity as a quasi-isometry invariant. The landed `kms-hb2` proof was
updated to use it.

Calibration: breadth-first search in `SL_4(F_p)` for `p = 3, 5, 7, 11` recomputes the orders and girths.

## Literature boundary

- Web searches found Kangaslampi–Vdovina (arXiv:1409.1401), Kangaslampi (arXiv:1410.4655), and
  Constantine–Lafont–Oppenheim (arXiv:1407.3958, withdrawn by the authors for an error in Fact 3). All of them
  are about triangular or Fuchsian buildings.
- `Y` here is not a building: its links are opposite-chamber subgraphs of generalized polygons (CCKW
  Proposition 7.1).
- The CCKW extraction contains no "surface". Nothing on surface subgroups of KMS groups was found.
- Not searched: MathSciNet/zbMATH, and papers citing CCKW after 2023.

## Exact gaps and next steps

1. **`G_HC2(1)(p)` and `G_HBC2(2)(p)`.** There is no `{±1, ±2}` labelling at `T = 24`. MSI job 788598 runs
   labels `{±1, ±2, ±3}` at `T = 24`, and `T = 48` for `G_HC2(1)`. A label `±3` excludes `p = 3` only.
   Alternatives: mod-`p` labellings for a fixed `p`, or larger `T`.
2. **Presentations.** For the five families other than `G_HB2(2)`, the commutator words were read from the text
   extraction and not cross-checked against a compiled presentation.
3. **KMS groups over `F_q`, `q = p^e`**, and generalized triangle groups with other unipotent vertex groups.
   The integer lift covers prime fields only. Over `F_q`, the vertex groups contain `U(p)`-type subgroups only
   for suitable root subgroups.
4. **Gromov's question itself** stays open. This covers infinite families of rigid hyperbolic groups, not a
   structural class such as all hyperbolic Kazhdan groups or all hyperbolic 2-dimensional triangle groups.
