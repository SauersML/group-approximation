# CCKW trivalent triangle groups marked VTF "?": vertex-injective finite quotients (2026-09-14)

Lane `hl-hyperbolic-rf-2`. Computer-assisted, unreviewed.
- Scripts, inputs, certificates and extracted outputs are in `experiments/cckw-vtf-certificates/`.
- Everything was computed on MSI: Slurm partition `agsmall`, GAP 4.14 from `sagemath/10.7`, LINS 0.9
  installed under the lane's scratch directory, and the verifier run with `/usr/bin/python3.12`.

## 1. Why

- **Target.** The graph target is `hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free`, the
  hyperbolic Neumann–Neumann problem. Through `simple-vertex-triangles-are-universal-for-triangle-vtf` it is
  equivalent to `hyperbolic-simple-triangle-group-without-finite-quotients`, which feeds Gromov's question.
- **The best-studied literature candidates of this shape.** Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276,
  tabulate the trivalent triangle groups `G = <a,b,c | a^3, b^3, c^3, R_ab, R_bc, R_ca>`. The vertex groups
  `<a,b>`, `<b,c>`, `<c,a>` act simply transitively on the edges of cubic link graphs.
  - Their tables have a column `VTF` with entries `Yes` or `?`, and the source never defines the column.
  - Their virtual torsion-freeness criterion is Theorem 3.1(iv), verbatim from `SmallHyp.tex`, line 643:
    "If there is a homomorphism $\psi \colon G \to F$ to a finite group, whose restriction to $G_{v_i}$ is
    injective for each $i=0, 1, 2$, then $G$ is virtually torsion-free."
  - On main this is (iv) of `triangle-of-groups-half-girth-structure` (ESTABLISHED, literature import).
- **Products.** Let `ψ_1, …, ψ_m` be homomorphisms to finite groups. If for each vertex group `X_i` the
  kernels `ker(ψ_j|X_i)` intersect trivially, then `(ψ_1, …, ψ_m)` is injective on every `X_i`. On disjoint
  point sets this is one permutation representation.

## 2. Sources (read on MSI)

- **The arXiv source** of 2011.09276, downloaded on 2026-09-13 to
  `/scratch.global/sauer354/ex/ex-hyperbolic-triangle-search/cckw/src/`.
  - The abs page lists v1 and v2, and the files do not name their version.
  - md5 sums:

    | file | md5 |
    |---|---|
    | `SmallHyp.tex` | `41f55906a45091e360b534a2eff3e0de` |
    | `table_3_3_4.tex` | `1fa9de804597c0ef73b5648ab184f7b8` |
    | `presentations_3_3_4.tex` | `db4202d70624fe1a35682a3ac5ec2fd7` |
    | `table_3_4_4.tex` | `a161163ceaf84a714830a4e4ba823a90` |
    | `presentations_3_4_4.tex` | `9a263f8dda44f92a188c9173336babdb` |
    | `table_4_4_4.tex` | `d8fe33169e14ed84189ec606ee7f41a8` |
    | `presentations_4_4_4.tex` | `c53ab406bfeb88634282dd31fa303fcf` |

- **The published version** is J. London Math. Soc. (2) 106 (2022), 3577–3637 (TU Berlin deposit PDF;
  received 5 January 2021, revised 15 February 2022). Its abstract says: "Appendices A, B and C are provided
  separately as supplementary material with the published article." The tables are in those appendices,
  which were not read. The `?` entries here are those of the arXiv source.
- **Follow-up literature.** Web search on 2026-09-14 found no later paper settling these entries. The
  search was bounded (two queries plus Witzel's publication page), so treat this as "none found".
- **The groups marked VTF `?`.** The tables have 53 of 78 groups of half-girth type (3,3,4), 16 of 54 of type
  (3,4,4) and 5 of 17 of type (4,4,4). In every type `Σ 1/r_i < 1`, so by Theorem 3.1(v) every group is
  non-elementary hyperbolic.

## 3. Method

1. **Presentations.** `experiments/hyperbolic-triangle-search/cckw_convert.py` turns the TeX presentations
   into GAP words (`cckw334_q.g`, `cckw344_q.g`, `cckw444_q.g`; `names_other.py` selects the `?` rows of
   the latter two tables).
   - A vertex group with link label `n` has order `3n/2`.
   - GAP computes the vertex orders from the vertex relators in every run (`|V|=` in `summary.txt`), and
     `experiments/hyperbolic-triangle-search/cckw_vertex.out` records them for all labels.
2. **Listed simple quotients** (`parse_targets.py`, `gq_vtf.g`).
   - For each `?` group, compute all epimorphism classes (GAP `GQuotients`) onto each simple group in
     CCKW's `L_2`-quotient and small-quotient columns.
   - Record each epimorphism's vertex image orders and the orders `K` of the kernel intersections on the
     three vertex groups.
3. **All small quotients** (`lins_vtf.g`). Enumerate all normal subgroups of index `<= 10^4` with LINS,
   which also finds non-simple quotients such as central lifts, and apply the same test.
4. **Certificates.**
   - `cert_vtf.g` exports the smallest vertex-injective LINS quotient, in a smaller-degree permutation
     representation.
   - `cert_product.g` greedily keeps epimorphisms onto listed quotients while they shrink a kernel
     intersection, and concatenates them on disjoint points.
   - `lift_vtf.g`, with specs in `lift_specs.g`, handles groups whose listed quotients leave only a
     central kernel on a vertex group.
     - It forms a quasisimple cover `H`: `SL(n,q)`, `SU(n,q)`, or `2.A_n` from GAP's basic spin
       representation.
     - It computes all epimorphisms onto `H/Z(H)`, sends `a, b, c` to preimages of order 3, and keeps the
       lifts that satisfy every relator.
     - It exports a vertex-injective lift.
5. **Independent verification** (`verify_vtf_cert.py`, no GAP). The verifier checks three things:
   - the permutations satisfy every relator;
   - `<a,b>`, `<b,c>`, `<c,a>` have orders `3n/2`, so the homomorphism is injective on the vertex groups;
   - the coset graphs of the images have girths `2r_i` with `Σ 1/r_i < 1`.

## 4. Calibration and controls

- **LINS on VTF `Yes` groups** (index bound 3000, `smoke.out`).
  - `G_0^{14,14,40}`, `G_4^{14,14,40}` and `G_0^{14,24,40}` each have a vertex-injective quotient `A_7` at
    index 2520.
  - `G_0^{14,18,40}` shows none below 3000, which is consistent: CCKW's listed quotient is `J_2`, of
    order 604800.
- **Positive verifier control.** `certs/ctl_g0_14_24_40.cert` is the exported `A_7` quotient of the `Yes`
  group `G_0^{14,24,40}`, of degree 7. Result: `CERTIFICATE VALID`.
- **Negative verifier control.** `certs/neg_ctl.cert` is the same file with `c` overwritten by `b`.
  - Two relators fail, and the vertex orders come out `[21, 3, 21]` against `[21, 36, 60]`.
  - Result: `CERTIFICATE INVALID`, exit 1.
- **`GQuotients` completeness.** Epimorphisms are listed up to `Aut(S)`, and composing with an automorphism
  changes neither the kernels nor the vertex image orders. So `K` is exactly the intersection over all
  epimorphisms onto the listed targets.

## 5. Results

### 5.1 Twenty-three `?` groups are virtually torsion-free (certificates verified)

All certificates print `CERTIFICATE VALID` with exit code 0 (`summary.txt`, section "verifier outputs").

| type | group | quotients used | degree | md5 of certificate |
|---|---|---|---|---|
| (3,3,4) | `G_0^{14,14,48}` | lift of the `A_7` epimorphism to `2.A_7` (`lift_vtf.g`) | 240 | `6de6e6bdd1786192ebb1fc93656cd7d0` |
| (3,3,4) | `G_4^{14,14,48}` | LINS normal subgroup of index 5040; quotient `2.A_7` (GAP: `C2 . A7`) | 240 | `c8993d5290d10b063cdba611e3fe4971` |
| (3,3,4) | `G_5^{14,14,48}` | lift of the `A_8` epimorphism to `2.A_8` (`lift_vtf.g`) | 240 | `5bd0bde2969fe5dfa7cb89614cea8206` |
| (3,3,4) | `G_0^{16,16,48}` | `PSL(3,3)`, `A_9` (found by the 44 GB rerun) | 22 | `cd6bb7ad138297eee0d57a613a51b011` |
| (3,3,4) | `G_0^{16,16,54}` | `PSL(3,3)`, `PSp(4,3)` | 53 | `e2c95f95f0a672e9ed14697eb9d23367` |
| (3,3,4) | `G_0^{16,18,48}` | `PSL(3,3)`, `A_10` | 23 | `bc6c5da70abad18c3f69175f43aa8439` |
| (3,3,4) | `G_0^{16,24,48}` | `A_9`, `PSp(6,2)` (one `PSp(6,2)` is injective alone) | 72 | `dea2d01734f56b5828e3d2bebf87000a` |
| (3,3,4) | `G_2^{16,24,54}` | `PSp(4,3)`, `A_10` | 50 | `f0848b7d7d648896ece66286da8900d8` |
| (3,3,4) | `G_0^{18,18,48}` | `PSL(3,3)`, `A_10` (44 GB workspace) | 23 | `db59d3cfc61694c6ebd4ed0f780ab7ec` |
| (3,3,4) | `G_4^{26,26,48}` | `PSL(2,13)`, `PSL(3,3)`, `G_2(3)` | 378 | `080d50d9b232c5c1f52448275055fdc5` |
| (3,3,4) | `G_5^{26,26,48}` | lift of the `PSL(4,3)` epimorphism to `SL(4,3)` (`lift_vtf.g`) | 80 | `e3acc333fa08cf3086387681e61fb51e` |
| (3,4,4) | `G_0^{16,40,48}` | `PSL(2,9)`, `M_11` | 21 | `da815b6f7d125eb677cc91f23df0f236` |
| (3,4,4) | `G_0^{18,40,54}` | `PSp(4,3)`, `M_12` (one `PSL(4,3)` is injective alone) | 52 | `38d18cd722063c075f13752ab5ce6fb0` |
| (3,4,4) | `G_0^{18,54,54}` | `PSL(3,3)`, `A_9` | 22 | `a08f384a656eac8302fb06d2fe6b55a5` |
| (3,4,4) | `G_2^{24,48,54}` | `PSp(4,3)`, `A_9` | 49 | `87acbb1e745c202c99d47cada0da82b6` |
| (3,4,4) | `G_0^{24,54,54}` | two epimorphisms onto `A_9` | 18 | `3b396533d5ad5ef3650273d0fe07d740` |
| (3,4,4) | `G_2^{24,54,54}` | `PSp(4,3)`, `A_9` | 49 | `2c75979400229116fcbf72d99aeee368` |
| (3,4,4) | `G_2^{26,48,54}` | `G_2(3)`, `PSL(4,3)` | 391 | `c67589460650865e9cc2bb1ad16f37a4` |
| (4,4,4) | `G_0^{48,48,48}` | `PSL(3,3)`, `PSp(4,3)`, `PSp(4,3)` (44 GB workspace) | 93 | `9bb50b1932f0be777c02444506407931` |
| (4,4,4) | `G_0^{48,54,54}` | `PSL(3,3)`, `PSp(4,3)`, `PSp(4,3)` | 93 | `4486c77c3c0e4aeacccff79691bc6b4c` |
| (4,4,4) | `G_8^{48,54,54}` | `PSL(3,3)`, `PSp(4,3)`, `PSp(4,3)` | 93 | `756064b44f2cd9f2664824d26428a111` |
| (4,4,4) | `G_0^{54,54,54}` | `PSL(3,3)` and two epimorphisms onto `A_9` | 31 | `eb5e3ad4a077263d8b65bc7d52b14c71` |
| (4,4,4) | `G_2^{54,54,54}` | `PSL(3,3)`, `PSp(4,3)` | 53 | `d678de2326d67687b8d8e837094593ec` |

**Remarks.**
- **Non-simple quotients matter.** For `G_4^{14,14,48}` the only listed simple quotient, `A_7`, is not
  injective on the order-72 vertex group `C3 x SL(2,3)`: it kills its central involution. The central
  extension `2.A_7` is injective on all three vertex groups.
- **Most `?` entries decided here need no search beyond CCKW's own list.** A product of two or three of the
  simple quotients they list is already injective.

### 5.2 The 51 undecided `?` groups (as of this version)

`e` is the number of epimorphism classes onto listed simple quotients, and `K` the kernel-intersection
orders from §3.2. When `e = 0`, `K` is the vertex orders.

- **LINS column.** It gives the number `q` of nontrivial normal subgroups of index `<= 10^4` and their `K`.
  The LINS array covers only the (3,3,4) table, and `pending` means the task had not finished at this version.
- **Incomplete rows.** The listed quotients were not all tested for two groups:
  - `G_0^{16,26,40}` and `G_0^{26,40,48}` list `2F4(2)'`, which GAP's `SimpleGroup` cannot construct;

| type | group | `e` | `K` (listed quotients) | LINS (index `<= 10^4`) |
|---|---|---|---|---|
| (3,3,4) | `G_1^{14,14,48}` | 2 | `[1,1,3]` | `q=9`, `[1,1,3]` |
| (3,3,4) | `G_0^{14,14,54}` | 1 | `[1,1,3]` | `q=2`, `[1,1,3]` |
| (3,3,4) | `G_4^{14,14,54}` | 0 | `[21,21,81]` | `q=2`, `[1,1,27]` |
| (3,3,4) | `G_0^{14,16,40}` | 1 | `[1,2,1]` | `q=0` |
| (3,3,4) | `G_0^{14,16,48}` | 0 | `[21,24,72]` | `q=5`, `[1,1,3]` |
| (3,3,4) | `G_1^{14,16,48}` | 1 | `[1,2,6]` | pending |
| (3,3,4) | `G_0^{14,16,54}`, `G_2^{14,16,54}` | 0 | `[21,24,81]` | `q=1`, `[7,8,27]` |
| (3,3,4) | `G_0^{14,18,54}`, `G_2^{14,18,54}` | 0 | `[21,27,81]` | `q=9`, `[1,1,3]` |
| (3,3,4) | `G_0^{14,24,48}` | 0 | `[21,36,72]` | pending |
| (3,3,4) | `G_0^{14,24,54}` | 0 | `[21,36,81]` | `q=7`, `[1,4,9]` |
| (3,3,4) | `G_0^{14,26,40}`, `G_4^{14,26,40}` | 0 | `[21,39,60]` | `q=0` |
| (3,3,4) | `G_0^{14,26,48}`, `G_1^{14,26,48}`, `G_4^{14,26,48}`, `G_5^{14,26,48}` | 0 | `[21,39,72]` | `q=1`, `[7,13,24]` |
| (3,3,4) | `G_0^{14,26,54}`, `G_2^{14,26,54}`, `G_4^{14,26,54}`, `G_6^{14,26,54}` | 0 | `[21,39,81]` | `q=1`, `[7,13,27]` |
| (3,3,4) | `G_0^{16,18,54}`, `G_2^{16,18,54}` | 7 | `[1,1,3]` | pending |
| (3,3,4) | `G_0^{16,26,40}` | 1 (`PSL(2,169)`; `2F4(2)'` untested) | `[2,1,1]` | pending |
| (3,3,4) | `G_0^{16,26,48}` | 1 | `[2,1,6]` | pending |
| (3,3,4) | `G_1^{16,26,48}` | 0 | `[24,39,72]` | pending |
| (3,3,4) | `G_0^{16,26,54}`, `G_2^{16,26,54}` | 0 | `[24,39,81]` | pending |
| (3,3,4) | `G_0^{18,18,54}` | 5 | `[1,1,3]` | pending |
| (3,3,4) | `G_0^{18,26,40}` | 0 | `[27,39,60]` | pending |
| (3,3,4) | `G_0^{18,26,54}`, `G_2^{18,26,54}` | 5 | `[1,1,3]` | pending |
| (3,3,4) | `G_0^{24,26,40}` | 1 | `[3,1,1]` | pending |
| (3,3,4) | `G_0^{24,26,48}` | 2 | `[1,1,2]` | pending |
| (3,3,4) | `G_1^{24,26,48}` | 0 | `[36,39,72]` | pending |
| (3,3,4) | `G_2^{24,26,54}` | 0 | `[36,39,81]` | pending |
| (3,3,4) | `G_0^{26,26,40}` | 0 | `[39,39,60]` | pending |
| (3,3,4) | `G_0^{26,26,48}` | 3 | `[1,1,3]` | pending |
| (3,3,4) | `G_1^{26,26,48}` | 0 | `[39,39,72]` | pending |
| (3,3,4) | `G_0^{26,26,54}` | 2 | `[1,1,3]` | pending |
| (3,3,4) | `G_4^{26,26,54}` | 3 | `[1,1,3]` | pending |
| (3,4,4) | `G_0^{14,40,48}` | 4 | `[1,1,2]` | not run |
| (3,4,4) | `G_1^{14,48,48}` | 0 | `[21,72,72]` | not run |
| (3,4,4) | `G_0^{14,48,54}` | 1 | `[1,1,3]` | not run |
| (3,4,4) | `G_0^{14,54,54}`, `G_8^{14,54,54}` | 0 | `[21,81,81]` | not run |
| (3,4,4) | `G_0^{26,40,48}` | 1 (`PSL(2,169)`; `2F4(2)'` untested) | `[1,1,6]` | not run |
| (3,4,4) | `G_2^{26,40,54}` | 0 | `[39,60,81]` | not run |
| (3,4,4) | `G_0^{26,48,54}` | 1 | `[1,1,3]` | not run |
| (3,4,4) | `G_0^{26,54,54}` | 5 | `[1,3,3]` | not run |

For `G_0^{16,26,40}` and `G_0^{26,40,48}` the value of `K` comes from the one `PSL(2,169)` epimorphism, read from
the partial output.

## 6. What stays open

- **No literature candidate of this shape is shown quotientless.** The strongest surviving candidates
  have no nontrivial quotient in any search: no listed simple quotient, and no normal subgroup of index
  `<= 10^4` for the rows marked `q=0`. These are the CCKW-style targets for the Neumann–Neumann problem,
  and the natural next tests are the trace-ideal certificates of `linear-quotient-exclusion-lifts-from-char-zero`.
- **Cover lifts** (`lift_vtf.g`, `summary.txt` section "lift_vtf.g"). Three groups certified. No lift that satisfies the
  relators and is injective on the vertex groups was found for the other ten groups tried:
  - `G_1^{14,14,48}`: `SL(2,7)`, and `SL(3,4)` (0 epimorphisms onto `PSL(3,4)`);
  - `G_0^{14,16,40}`: `SL(2,49)`;
  - `G_1^{14,16,48}`: `SL(2,7)`;
  - `G_0^{16,26,48}` and `G_0^{24,26,48}`: `SL(2,13)`, and `SL(4,3)` for `G_0^{24,26,48}`;
  - `G_0^{16,18,54}` and `G_2^{16,18,54}`: `SU(3,8)`;
  - `G_0^{14,40,48}`: `SL(2,49)` and `2.A_7`;
  - `G_0^{16,26,40}` and `G_0^{26,40,48}`: `SL(2,169)`.

  Every automorphism of `H/Z(H)` lifts to `H` for these covers, so lifting one representative of each class
  covers every epimorphism. Kernels of order 3 need 3-fold covers such as `3.A_7` or `3.PSL(3,4)`, and
  those were not tried.
- **Untested targets.** GAP cannot construct `2F4(2)'` by `SimpleGroup`, so that target was not tried for
  `G_0^{16,26,40}` and `G_0^{26,40,48}`. The three runs that hit the 12 GB workspace limit, or were still
  running, were redone with 44 GB and decided `G_0^{16,16,48}`, `G_0^{18,18,48}` and `G_0^{48,48,48}`.
