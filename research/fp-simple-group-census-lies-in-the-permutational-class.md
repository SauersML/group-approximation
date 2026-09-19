---
rg: 2
id: fp-simple-group-census-lies-in-the-permutational-class
kind: claim
title: Every family of finitely presented infinite simple groups in the literature census below lies in B_A, so joint embedding, squares and BFFHZ Question 3.4 hold across the whole census
distinct_from:
  fp-simple-groups-have-the-joint-embedding-property: that is the open statement (JE) for all finitely presented simple groups; this is its verification on a named census of known families, which cannot decide the open statement.
  boone-higman-closed-under-finite-direct-products: that is open product closure; this verifies it on the same census.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 in general; this verifies it family by family, through the equivalence with PBH for finitely presented simple groups.
---

**ESTABLISHED as a census** (lane bh-major-product, 2026-09-18; assembly of landed nodes; not
independently reviewed). Each row carries the conditions of its covering node.

**The census.**
- The sources are the families listed in the BBMZ survey (arXiv:2306.16356v3, l.26–33 and
  l.426–430 of the extracted text on MSI), together with later sources recorded on main.
- Every row is an infinite simple group whose finite presentation is published, or is proved
  on main where the row says so.
- A family counts as covered when every member, and hence every subgroup, lies in `B_A`.

| Family | Covering node | Rests on |
|---|---|---|
| `V`, `T`, Higman–Thompson, Brin `nV`, finite germ extensions of `V` | `fp-full-binary-cantor-groups-have-type-a-actions`, `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` (`T, V_(n,r) ≤ V`) | published finite presentation |
| Röver–Nekrashevych groups `V(G)`, including Scott's `Sc(n)`, Röver's group and Skipper–Witzel–Zaremsky (simple members) | BFFHZ Remark 3.5 as quoted in `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` (a Higman–Thompson commutator subgroup inside); contracting ones also by `hyperbolic-groups-lie-in-the-permutational-class` | finite presentation of `V(G)` |
| Twisted Brin–Thompson `SV_G` (Belk–Zaremsky) and the finitely presented simple quotients of FFWZ's `SV_A` | `twisted-btb-clopen-action-is-type-a` | Zaremsky's criterion |
| `k`-graph full groups with two loops of every colour at every vertex, including Matui's SFT groups `V_A` of that kind | `stabilized-kgraph-full-groups-have-type-a-actions` | Li `thm:deg` |
| BBMZ full contracting rational similarity groups | `hyperbolic-groups-lie-in-the-permutational-class` | refs a, b PASS |
| Stein `V`- and `T`-groups; Cleary and Burillo–Nucinkis–Reeves `T_τ`, `V_τ` | `stein-v-groups-act-with-type-a-on-breakpoints`, `interval-exchange-pl-groups-act-with-type-a-on-breakpoints`, `circle-pl-groups-act-with-type-a-on-breakpoint-orbits` | Li k-graph theorem (integral case); Pisot RSG route (golden ratio); Stein 1992 not needed |
| Finitely presented PL rearrangement groups | `pl-rearrangement-groups-have-two-transitive-orbit-actions` | their finite presentation |
| Lodha's circle group `S` | `lodha-simple-circle-group-has-a-type-a-action` | Lodha, read at source |
| Hyde–Lodha line groups `Q_n` | `hyde-lodha-simple-line-groups-lie-in-the-permutational-class` (**new**) | Li k-graph theorem |
| Burger–Mozes, Wise, Rattaggi, Radu, and every cocompact lattice in a product of two trees | `product-of-two-trees-lattices-satisfy-permutational-boone-higman`; for Burger–Mozes also BFFHZ Remark 3.5 | BLIW |
| Lattices in finite products of trees with a faithful factor | `product-of-trees-lattices-with-faithful-factor-satisfy-pbh` | BLIW |
| Amir–Lazarovich lattices | `tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh` | BLIW, lane proof |
| Titz Mite–Witzel kernels, and every irreducible Euclidean building lattice | `euclidean-building-lattices-lie-in-permutational-bh-class` | Le Bars–Leibtag–Vigdorovich MIF (preprint), or the lane proof with their topological freeness |
| Caprace–Rémy non-affine Kac–Moody groups | `fp-simple-kac-moody-lattices-satisfy-pbh` | Rybak's MIF theorem, re-read at source |
| `L_p^×/F_p^×`, `(L_p ⊗ L_p)^×/F_p^×` (Khanh; bh-free-26) | `leavitt-unit-groups-mod-scalars-satisfy-pbh`, `leavitt-square-unit-groups-mod-scalars-satisfy-pbh` (09-13) | Khanh preprint |
| `(L_p^(⊗d))^×/F_p^×`, `d >= 3` | `projective-leavitt-tensor-units-lie-in-the-permutational-class` | Khanh, FJ lane derivation, MMN |
| `W`, `D(W_(P,ℓ))` | `twisted-integral-affine-groups-lie-in-the-permutational-class` | finite presentation of `W` (lane proof) |

**Consequences** (under those conditions).
- **BFFHZ Question 3.4 holds for every group in the census.** By
  `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`, it is equivalent to PBH for a finitely
  presented simple group.
- **(JE), (SQ) and finite-product closure hold for every finite family drawn from the census.**
  `B_A` is closed under finite direct products and subgroups
  (`boone-higman-type-a-class-closed-under-finite-extensions`), and so is the finite-extension
  closure (FW). Free products also stay in `B_A` (BFFHZ Corollary F).
- **Correction to `research/artifacts/gq-bh-bh-typeA-oligomorphic-q34-census-update.md`.** Its row
  "Rattaggi's simple lattices: not settled" concerns a type (A) action of the lattice itself.
  For PBH, and hence for Question 3.4, Rattaggi's `Σ_0 ≤ Σ` has been settled since 09-13 by the
  two-trees node, as has every cocompact lattice in a product of two trees.

**Checked and found not to be sources of finitely presented simple groups.**
- Matte Bon–Triestino's `T(φ)` (arXiv:1811.12256). Its abstract says that "for every minimal
  subshift, the corresponding group is never finitely presentable".
- Hyde–Lodha's finitely generated simple groups `G_ρ` of homeomorphisms of the line. There are
  uncountably many of them, so all but countably many are not finitely presented, and none is
  known to be.
- Derived subgroups of full groups of minimal subshifts. No finitely presented example is
  known.
- The dendrite rearrangement groups `G_n` are finitely presented, but not simple. Finite
  presentation of their simple commutator subgroups is open, and in any case `G_n ≤ V`
  (`dendrite-rearrangement-groups-are-finitely-presented`).
- No "Bux–Mischler" family of finitely presented simple groups was found. A web search on
  2026-09-18 returned only Bux's finiteness papers.

**Where coverage is weakest** (updated 2026-09-18, after reading the three weakest links at source).
No published family is uncovered. For each of the three links named earlier, here is what it rests
on now.
1. **Titz Mite–Witzel kernels: two routes.**
   - *MIF route.* `titz-witzel-kernels-are-mif`, through Le Bars–Leibtag–Vigdorovich
     arXiv:2609.17129 `Thm:MIF` (`exotic-rank-two-building-lattices-are-mif`), then BFFHZ Theorem C.
     The authors draw this consequence themselves.
   - *Euclidean route.* bh-groupoid's lane proof. Its topological-freeness input now comes from
     their `thm:gq-open-dense-opposite-geometry`, whose proof was read here line by line.
   - Neither route uses the Ciobotaru–Le Bars barycenter chain (trust note T1).
   - Remaining trust: an unrefereed preprint of September 2026, and Ciobotaru–Le Bars Prop. 6.1 for
     the MIF route. That proposition's written proof shows density of attracting chambers and then
     says the general-type condition "suffices". That step is the one to referee.
2. **Kac–Moody.** Rybak's chain was re-read at source (`fp-simple-kac-moody-lattices-are-mif`,
   "Source re-read"). The ping-pong and the micro-support lemmas check. What remains is the
   unrefereed preprint plus published inputs (Caprace–Fujiwara, Petyt–Spriano–Zalloum, Caprace 2007,
   Dymara–Schick).
3. **Stein-type groups.** No census coverage needs Stein 1992 any more.
   - Stein's `T`- and `F`-groups, and Hyde–Lodha's `Q_n`, lie in the integral `V`-groups. Those are
     `F_∞` by Li's k-graph theorem, read at source
     (`integral-slope-stein-v-groups-are-k-graph-full-groups`, lane proof).
   - `T_τ ≤ V_τ` and `V_τ` are covered by the golden-ratio instance (`β² = β + 1`, property (F)) of
     `pisot-number-slope-stein-groups-are-contracting-rsgs`, a lane proof.
   - Stein 1992 was not obtainable: the AMS server returned 403 to scripted requests. Tanner,
     arXiv:2312.07375 (read at source), attributes `F_∞` of the integral groups to it, and gives the
     k-graph identification.

The weakest remaining links are now the internal lane proofs:
- `integral-slope-stein-v-groups-are-k-graph-full-groups`;
- `pisot-number-slope-stein-groups-are-contracting-rsgs`;
- `euclidean-building-lattices-lie-in-permutational-bh-class`;
- finite presentation of `W`.

`W` does not threaten the census, since it only decides whether `W` is a member.

## Lesson for general BH

Every known way of *proving* that a simple group is finitely presented also yields a type (A)
actor. The four ways are:
- a Stein–Farley complex, whose breakpoint or clopen action is oligomorphic;
- Bass–Serre theory, with BLIW's rigid tree overgroup;
- building lattices, through a boundary coding or high transitivity;
- Steinberg presentations over Leavitt rings, through a Cantor module.

So, within the literature, PBH is not a separate question from finite presentation. A
separation of BH from PBH, or a failure of (JE) or (SQ), needs a fifth construction principle:
a finitely presented simple group with no oligomorphic complex, no tree, no building, and no
Cantor-module ring behind it. The target to watch is the first such construction.
