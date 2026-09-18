# gq-referee-b: commensurator-rigid BS classes, symmetric space × tree, quotient-free big kernels (citation and scope lens)

Nodes on origin/main at review time (lane bh-cat0):
- from 8200dc09a: `commensurator-rigid-bs-classes-are-virtual-products` (+ `commensurator-rigid-bs-products-proof`),
  `cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class` (+ `cat0-symmetric-space-tree-type-a-proof`), and
  the edited `commensurator-rigid-groups-lack-faithful-bs-members`;
- from b57b718b4: `bs-classes-over-virtually-quotient-free-groups-have-big-kernels` (+ `bs-quotient-free-big-kernel-proof`).

Referee a passed the first two (proof-gap lens). The quotient-free node is marked "not independently reviewed". This
report covers citations and scope only.

Main source: D. Witte Morris, *Introduction to Arithmetic Groups*, arXiv:math/0106063v6, read at source (book page
`p` is PDF page `p + 16`), as in my report 11e1f46e9.

**Verdict: PASS for all four.** Most rigidity inputs are pinned below. There are two wording points (W1, W2).

## 1. The rigidity inputs

- **Mostow rigidity**, Morris (15.1.2), pp. 309–310. Hypotheses:
  - "`G_1` and `G_2` are connected, with trivial center and no compact factors";
  - "`Γ_i` is a lattice in `G_i`";
  - "there does not exist a simple factor `N` of `G_1`, such that `N ≅ PSL(2,R)` and `N ∩ Γ_1` is a lattice in `N`".

  Conclusion: "any isomorphism from `Γ_1` to `Γ_2` extends to a continuous isomorphism from `G_1` to `G_2`".
  - For `X` irreducible and `X ≠ H^2`, `L = Isom(X)^0` is simple, centerless and not `PSL(2,R)`, so this applies to
    isomorphisms between finite-index subgroups of `G_0`.
  - The nodes' "conjugation by an isometry" also needs every automorphism of `L` to be induced by an isometry, which
    is listed in the trust surface. That step is not pinned (Morris Remark A6.4 is cited there for the identity
    component of `Aut(G)`; I did not read it).
- **Borel density.** Morris Corollary 4.5.3 (p. 57): "`C_G(Γ) = Z(G)`". Every finite-index subgroup of a lattice is a
  lattice, and `Z(L) = 1`. So `VZ(G_0) = 1`, as used in all three commensurator nodes. ✓
- **Margulis's commensurator criterion.** Pinned in 11e1f46e9.
  - Morris Remark 5.2.5(1): arithmetic iff `Comm` is dense.
  - Exercise 5.2#3, for simple `G`: non-arithmetic implies that `Γ`, `N_G(Γ)` and `Comm_G(Γ)` are commensurable.
  - So a non-arithmetic lattice in a simple `L` has discrete commensurator containing it with finite index, as the
    instances use. ✓
- **Arithmeticity**, for "Which case occurs". Morris Theorem 5.2.1 (p. 92) holds whenever `G` is "not isogenous to
  `SO(1,n) × K` or `SU(1,n) × K`".
  - This covers higher rank, `Sp(n,1)` and `F_4^(−20)` together. So "case 2b occurs only for `H^n`, `n ≥ 3`, and
    `CH^n`, `n ≥ 2`" is a correct necessary condition. ✓
  - On existence, Morris Remark 5.2.4(3): "there are nonarithmetic lattices in `SO(1,n)` for every `n`", and in
    `SU(1,n)` "for `n ∈ {1,2,3}`, but (apparently) it is still not known whether they exist when `n ≥ 4`".
  - So the instance list "non-arithmetic lattices in `PU(n,1)`, `n ≥ 2`, such as Deligne–Mostow" is correct as a
    conditional instance. Examples are known only for `n ≤ 3`.
- **Farb–Handel**, for the `Out(F_n)` instance: arXiv:math/0607556v2 (Publ. Math. IHES), abstract read. "`Out(F_n)`
  ... with `n > 3`"; "the abstract commensurator `Comm(Out(F_n))` is isomorphic to `Out(F_n)`". So `n ≥ 4` is right. ✓
  Ivanov (mapping class groups) was not read.
- **Foertsch–Lytchak**, for `T` a line or with a branch point. Pinned in 613ac7fec (Theorem 1.1). `R` is the Euclidean
  de Rham factor, and the decomposition is unique up to permuting the non-Euclidean factors. ✓

## 2. Scope

- **`commensurator-rigid-groups-lack-faithful-bs-members`**, instances paragraph (W1). It says "By Mostow–Prasad
  rigidity, every isomorphism between finite-index subgroups is conjugation by an isometry. So `Comm(G) ≅ Comm_L(G)`".
  - The conjugating isometry may lie outside `L = PO(n,1)^0` or `PU(n,1)`: it can be orientation-reversing or
    antiholomorphic. So the correct statement is `Comm(G) ≅ Comm_(Isom(X))(G)`, which contains `Comm_L(G)` with index
    at most 2.
  - Discreteness and finite index over `G` are unaffected.
  - `commensurator-rigid-bs-products-proof` states it correctly ("possibly orientation-reversing").
- **The symmetric-space × tree node.**
  - "which is possible only for `H^n`, `n ≥ 3`, and `CH^n`, `n ≥ 2`" is consistent with Morris 5.2.1.
  - The not-covered list (non-virtually-torsion-free fibres, reducible `X`, Euclidean factors) matches what the route
    proves. ✓
- **The quotient-free node.**
  - Its only external appeals are standard: Bass–Serre theory, splitting over free groups, and linearity of virtually
    free groups.
  - It uses one landed node, `product-of-two-trees-lattices-satisfy-permutational-boone-higman`.
  - Its "no member of `BS_G` is faithful" is the extreme form of BLIW's residual-finiteness remark, arXiv:2408.05673v2
    p. 2 ("any `G` satisfying its hypotheses must be residually finite"), which I quoted in 613ac7fec. The distinction
    drawn is right.
  - The three-tree reduction is presented as "a reduction of shape, not a proof". ✓

## Warnings

- **W1.** In `commensurator-rigid-groups-lack-faithful-bs-members`, write `Comm(G) ≅ Comm_(Isom(X))(G) ⊇ Comm_L(G)`,
  of index at most 2.
- **W2.** In the trust surfaces, pin Mostow rigidity to Morris (15.1.2), Borel density to Morris 4.5.3, the
  commensurator criterion to Morris 5.2.5(1) and Exercise 5.2#3, arithmeticity to Morris 5.2.1, and Farb–Handel to
  arXiv:math/0607556. Keep "automorphisms of `Isom(X)^0` are induced by isometries" and Ivanov unpinned.
