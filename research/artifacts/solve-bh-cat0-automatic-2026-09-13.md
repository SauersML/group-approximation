# Boone--Higman for CAT(0) and automatic groups: lane solve-bh-cat0-automatic, 2026-09-13

Targets: BBMZ survey Problem 5.3, items (10) CAT(0) groups and (11) automatic
groups. Both were unstaffed with no node
(`bh-survey-open-cases-status-2026-09-12.md`).

Sources, fetched as arXiv TeX into `~/lanes/cat0/` on MSI:
- 2306.16356 (BBMZ survey);
- 2408.05673 (Bux--Llosa Isenrich--Wu, "BLIW");
- 1608.06265 (Bader--Caprace--Lécureux, "BCL");
- 2509.05054v2 (Titz Mite--Witzel, "TMW").

## 1. Verbatim pins

- **Survey, Problem `prob:summary`:** "Prove the Boone--Higman conjecture for:
  ... (10) CAT(0) groups. (11) Automatic groups. ..." Remark `rmk:solved`
  reports progress on (1), (2), (3), (4), (8) and (13) only.
- **BLIW Theorem A** (TeX l.228--236) lists "Baumslag--Solitar groups;
  free(finite rank)-by-cyclic groups; Leary--Minasyan groups. Euclidean triangle
  Artin groups."
- **BLIW Corollary `cor:Leary-Minasyan-groups`:** "All Leary--Minasyan groups
  constructed in \cite{LeaMin-21} satisfy the Boone--Higman Conjecture. In
  particular, there is a CAT(0) group that is not virtually biautomatic and
  satisfies the Boone--Higman Conjecture." The proof: "By construction the
  Leary--Minasyan groups are HNN-extensions of $\mathbb{Z}^n$ that identify two
  finite index subgroups."
- **BLIW Theorem `thm:free-groups`:** "every group in $\BSol_{\mathbb{F}_k}$
  embeds in a simple group of type $F_{\infty}$."
- **BLIW Remark `rem:burger-mozes`:** "for every group in
  $\BSol_{\mathbb{F}_k}$ the permutational Boone--Higman Conjecture holds". Main
  imports this as `free-generalized-bs-groups-have-type-a-overgroups`.
- **BCL Theorem `nonlinear`** (l.185--190): for a locally finite
  $\widetilde A_2$-building not associated to $\mathrm{PGL}_3(D)$ and a discrete
  cocompact $\Gamma$, "for any commutative unital ring $R$ and any $n \geq 1$,
  any homomorphism $\Gamma \to \GL_n(R)$ has a finite image."
- **BCL l.219:** "by an unpublished work of Yehuda Shalom and Tim Steger we know
  that every non-trivial normal subgroup of a lattice in an
  $\widetilde{A}_2$-building is of finite index."
- **TMW Theorem A** (l.197): five finite triangle complexes with exotic
  $\tilde C_2$ universal covers and non-residually-finite fundamental groups,
  whose "finite residual ... has finite index". Also: "Since the $\Gamma_i^q$
  are uniform building lattices they are $\CAT(0)$-groups and have Kazhdan's
  property~(T)."
- **TMW Corollary** (l.203): the finite residuals "are simple $\CAT(0)$ groups
  that have property (T)".
- **TMW l.1700:** "Lattices on (irreducible) Euclidean enjoy Kazhdan's property
  (T) \cite{Oppenheim}". The bibliography entry is `unpublished`.
- **TMW l.248:** "the irreducible lattices of products of trees first studied by
  Wise, Burger and Mozes ... are the first known non-residually finite lattices
  on two-dimensional buildings".
- **Novelty search.** One web search (Boone--Higman with CAT(0), lattices,
  products of trees) returned BLIW, BBMZ, BFFHZ and Zaremsky, and no statement
  about general CAT(0) groups or product-of-trees lattices.

## 2. Landed

| Node | Status |
|---|---|
| `product-of-two-trees-lattices-satisfy-permutational-boone-higman` (+ proof) | ESTABLISHED, not reviewed |
| `cat0-groups-satisfy-boone-higman` (root, item 10) | OPEN |
| `automatic-groups-satisfy-boone-higman` (root, item 11) | OPEN |
| `exotic-a2-lattices-satisfy-boone-higman` | OPEN |
| `titz-witzel-lattices-satisfy-permutational-boone-higman` (+ route from MIF) | OPEN |
| `titz-witzel-kernels-are-mif` | OPEN |

**The product theorem, in one line.** Split along one tree. The vertex groups
act on the other tree with finite stabilizers and finitely many orbits, so they
are virtually free and not virtually cyclic, hence commensurable with `F_2`.
Edge groups have finite index, so the lattice lies in `BS_(F_2)` and then in
`B_A` (Remark 12.7). This gives the permutational form for:
- Radu's non-residually-finite lattice `Gamma_R`;
- the Wise and Burger--Mozes lattices;
- every reducible lattice.

## 3. Coverage of item (10) after this lane

| Subclass | Status | Why |
|---|---|---|
| Hyperbolic CAT(0) groups | covered | BBMZ |
| Virtually special or virtually RAAG groups | covered | linear over Z |
| Leary--Minasyan groups | covered | BLIW corollary |
| Lattices in products of two trees | covered | this lane |
| Products of three or more trees, with a faithful factor | covered once edge stabilizers are shown finitely presented | BLIW Theorem B |
| Products of three or more trees, no faithful factor, vertex groups not residually finite | open | Theorem C needs residually finite vertex groups |
| Exotic Ã₂ lattices | open | no linear image; (T) gives FA; flats; conjecturally not residually finite |
| Titz Mite--Witzel C̃₂ lattices | open, reduced to MIF of the simple kernel | Theorem C plus finite-extension closure |
| Non-special cubulated groups, not of product type | open | no tree action with locally finite dual tree |

## 4. Exact gap

- **Item (10).** The first uncovered named groups are the Kazhdan building
  lattices. A finitely presented simple host for them must come from a new
  source.
  - **Boundary dynamics.** The chamber space at infinity is a Cantor set, and a
    group of germs of sector maps would be a Brin--Thompson-type candidate. Its
    finite presentation is untested.
  - **MIF of a finite-index subgroup,** plus a finitely presented simple MIF
    overgroup. For Titz Mite--Witzel the simple kernel is its own overgroup, so
    MIF of the kernel suffices.
- **Item (11).** Closed-surface mapping class groups of genus at least 3 are the
  first open named case. No method uses automaticity itself.
