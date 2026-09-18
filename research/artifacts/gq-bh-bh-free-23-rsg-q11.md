# BBMZ-hyperbolic Question 1.1: source notes and new cases (lane bh-free-23, 2026-09-18)

Source: Belk–Bleak–Matucci–Zaremsky, *Hyperbolic groups satisfy the Boone–Higman conjecture*,
arXiv:2309.06224v3. TeX read at `gq/src/bh-free-03/bbmz2-2309.06224.tex`. Labels are TeX labels.

## Questions (§1 `ssec:open`, verbatim)
- **Q1.1** "Is every non-elementary hyperbolic group isomorphic to a contracting RSG?" The text
  after it says that hyperbolic `G` acting faithfully on its Gromov boundary is isomorphic to an
  RSG, and contracting if `Z` is a proper free factor. It names the unknown irreducible core of
  `Σ_Γ` as the main impediment.
- **Q1.2** "Do full, contracting RSGs have type F∞?" This is open even for contracting
  Röver–Nekrashevych groups (Nekrashevych's conjecture).
- **Q1.3** "Does every finitely presented subgroup of the rational group R_{Γ,E} embed in a
  finitely presented subgroup whose action on some orbit in E is oligomorphic and has finitely
  generated stabilizers of finite subsets?"
- **Q1.4** "If G is a finitely presented RSG, then must the full closure of G also be finitely
  presented?" This is the RSG analogue of Scott's theorem that `V_d(G)` is finitely presented for
  finitely presented self-similar `G`.

## Inputs used
- `def:full`, `def:rsg`, `def:contracting`, and the irreducible-core definition (conditions
  (i)–(iii)).
- `prop:fin_many_types` (BBM Cor 3.28).
- `thrm:BBM`: with no isolated points, the action is rational.
- `prop:hyp_similarities`: the image is an RSG.
- `thrm:contracting`: hyperbolic plus no isolated points gives finite nucleus.
- `rmk:horofunction_problems`: no finite normal subgroup gives a faithful action on `∂_h`, via
  Webster–Winchester.
- `lem:ConesAreAtoms`, `lem:atoms_in_atoms` and `thrm:FreeProductBoundary`: the `G * Z` case,
  whose proofs are adapted here.

## Landed nodes
- `free-products-with-a-finite-factor-are-contracting-rsgs` (+ proof): `G * F` with `F` finite.
  This is the finite-factor analogue of `thrm:FreeProductBoundary`. The `F`-cosets are cliques,
  so every vertex is a cut vertex between its `G`-branch and its `F`-clique.
- `contracting-rsgs-closed-under-products-with-finite-groups` (+ proof): `H × F`, built from
  `|F|` labelled copies of `E` under a new root.
- `non-elementary-hyperbolic-groups-are-contracting-rsgs` (OPEN): Q1.1 itself, with the known
  cases and the remaining gap.

## Q1.4 note (no claim)
A natural test case is `G = V ⋊ ⟨φ⟩` with `φ` a homeomorphism normalizing `V`: a
bi-synchronizing transducer of infinite order in `Out(V) ≅ O_2`.
- **What holds:** `G` is a finitely presented RSG, since it contains `V`.
- **The point of interest:** its nucleus is infinite as soon as the core size of `φ^k` is
  unbounded. So BBMZ's finiteness theorem does not apply to `[[G]]`. Finite presentation of
  `[[G]]` is then exactly the open content of Q1.4 for this family.
- **What was not decided:** I checked neither finite presentation of `[[G]]` nor an obstruction.

## Update (second landing): every free product
`free-products-of-hyperbolic-groups-are-contracting-rsgs` (+ proof
`hyperbolic-free-product-contracting-rsg-proof`) covers `A * B` for any two nontrivial
hyperbolic groups, not both of order 2.
- **The universal type** is the shadow `Sh(q)`, the atom of `q` at level `|q|`, for `q = y b`
  just past a syllable change. It depends only on the radius-1 geometry of `Cay(B)` at `b`.
- **Calibration:** for `B = Z` the shadow is BBMZ's `C(w)`, and for a finite factor with clique
  generators it is the branch `D^A_q`.
- **Consequence:** Q1.1 now holds for every freely decomposable non-elementary hyperbolic group,
  and for its products with finite groups.
- **What remains:** freely indecomposable groups, i.e. one-ended groups and splittings only
  over nontrivial finite groups, and non-split finite radicals.

## Update (third landing): finite-index overgroups
- `contracting-rsgs-closed-under-finite-index-overgroups` (+ proof): the induced action on one
  labelled copy of `E` per coset. Each element acts on each copy by an element of `H`, so the
  nucleus stays inside `Nuc_H`, and `g = t_j h t_i^{-1}` supplies the RSG moves.
- `virtually-free-product-hyperbolic-groups-are-contracting-rsgs` (+ proof): every
  non-elementary virtually free group is a contracting RSG, including `SL_2(Z)` and `GL_2(Z)`.
  So is every virtually torsion-free hyperbolic group with infinitely many ends.
- **Q1.1 now reduces to the one-ended case**, apart from hypothetical infinitely-ended
  hyperbolic groups that are not virtually torsion-free.
- **One-ended attempt** (Attempt 2 on the Q1.1 node): Bowen–Series-type Markov codings satisfy
  the RSG condition automatically, since `g_β^{-1} g_α` is the canonical similarity. Rationality,
  the finite nucleus and irreducibility remain unverified.
