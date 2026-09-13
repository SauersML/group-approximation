# The CCKW (6,6,8) trivalent triangle groups with no simple quotient found: data and an eigenvalue filter

Lane `ex-hyperbolic-triangle-search`, 2026-09-13. Computed with GAP 4.14 on MSI. Code and output are in
`experiments/hyperbolic-triangle-search/cckw_*`. This artifact is calibration data and a filter; it does not decide
any group.

## 1. Why these groups

By `simple-vertex-triangles-are-universal-for-triangle-vtf`, a hyperbolic triangle of finite groups
becomes a member of the target class of `hyperbolic-simple-triangle-group-without-finite-quotients` once
its vertex groups are amalgamated into alternating groups. It is quotientless exactly when its
edge-generated core has no vertex-injective finite quotient. Caprace–Conder–Kaluba–Witzel,
arXiv:2011.09276, §5.1, state: "for some of the hyperbolic groups with girth triple (4,8,8), (6,6,6)
and (6,6,8) on our list, we could not find any (non-abelian) finite simple quotient at all". So these
are the literature's best-studied candidates of this shape.

## 2. The 19 groups of half-girth type (3,3,4)

- **Source.** The arXiv source (`/scratch.global/sauer354/ex/ex-hyperbolic-triangle-search/cckw/src/`),
  files `table_3_3_4.tex` and `presentations_3_3_4.tex`.
- **Criterion.** Empty `L_2`-quotient column, empty "small quotients" column (simple quotients up to order
  `5·10^7`), and alternating-quotient degrees contained in `{3, 4}` (checked up to degree 30).
- **The groups.** Their names follow the paper:

`G_4^{14,14,54}`, `G_0^{14,16,48}`, `G_0^{14,16,54}`, `G_2^{14,16,54}`, `G_0^{14,18,54}`,
`G_0^{14,24,48}`, `G_0^{14,26,40}`, `G_4^{14,26,40}`, `G_0^{14,26,48}`, `G_1^{14,26,48}`,
`G_4^{14,26,48}`, `G_5^{14,26,48}`, `G_0^{14,26,54}`, `G_2^{14,26,54}`, `G_4^{14,26,54}`,
`G_6^{14,26,54}`, `G_1^{16,26,48}`, `G_0^{16,26,54}`, `G_0^{18,26,40}`.

**Presentations.**
- `cckw_convert.py` translates the TeX relators into GAP words (`cckw334.g`).
- Every group is `<a,b,c | a^3, b^3, c^3, R_ab, R_bc, R_ca>`, with vertex groups `<a,b>`, `<b,c>`, `<c,a>`.
- The labels are the numbers of vertices of the links: 14 (Heawood), 16 (Möbius–Kantor),
  18 (Pappus), 24 (Nauru), 26 (F26A), 40, 48, 54 (Gray).

**Vertex groups** (`cckw_vertex.out`). In every group the three vertex girths come out `6, 6, 8`,
matching the type:

| link label | order | structure (GAP) |
|---|---|---|
| 14 | 21 | `C7 : C3` |
| 16 | 24 | `SL(2,3)` |
| 18 | 27 | `(C3 x C3) : C3` |
| 24 | 36 | `C3 x A4` |
| 26 | 39 | `C13 : C3` |
| 40 | 60 | faithful irreducible degrees 3, 3, 4, 5, consistent with `A5` |
| 48 | 72 | `C3 x SL(2,3)` |
| 54 | 81 | `(C3 x C3 x C3) : C3` |

## 3. Edge-eigenvalue filter for vertex-faithful irreducible representations

Suppose `φ: G -> GL_d(C)` is faithful and irreducible on each vertex group.
- Its vertex characters `χ_ab, χ_bc, χ_ca` are faithful irreducibles of degree `d`.
- Each edge generator has the same eigenvalue multiplicities, over the powers of `E(3)`, in the two vertex modules
  containing it.
- The multiplicities come from the character values: `m_k(g) = (1/3) Σ_j χ(g^j) E(3)^{−kj}`.

`cckw_compat.g` counts the compatible triples for `d = 2, …, 6` (`cckw_compat.out`).

| groups | compatible triples, `d = 2..6` |
|---|---|
| the 16 groups other than the three below | 0 in every dimension |
| `G_0^{14,26,40}`, `G_4^{14,26,40}`, `G_0^{18,26,40}` | 16 in `d = 3`, 0 otherwise |

**Consequence (unreviewed).** Take any of the 16 groups and any `d <= 6`.
- No homomorphism `G -> GL_d(C)` is faithful and irreducible on all three vertex groups.
- This is a necessary-condition argument, so no Gröbner computation is involved.
- The mechanism is the same as the sign invariant of `hyperbolic-triangle-linear-search-2026-09-13.md` §3: the
  eigenvalue types of a shared edge generator disagree between its two vertex groups.
- For example, in `G_4^{14,14,54}` the Gray vertex `C3≀C3` gives `a` a repeated eigenvalue in every faithful
  3-dimensional irreducible, while the Heawood vertex gives `a` three distinct eigenvalues.
- In the same way, characteristic `p` coprime to the vertex orders gives no such representation for
  `d <= 6`, because the modular theory is ordinary.

**Not covered.**
- Representations that are faithful but reducible on some vertex group, for example `2 ⊕ 1` for `SL(2,3)`.
- Characteristics dividing the vertex orders (2, 3, 5, 7, 13).
- Dimensions `d >= 7`.

**The three survivors.** In all three the `ca` vertex is the order-60 group
with its two 3-dimensional irreducibles. Compatible triples exist in `d = 3`, so the next test is the
trace ideal of the torus parametrisation, as in `lin4.py` and `linD.py`, over `F_p` with
`p ≡ 1 mod 5460`. A point with faithful vertex modules gives a vertex-injective finite quotient of a
CCKW group for which CCKW found no simple quotient.
