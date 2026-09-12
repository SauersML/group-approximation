# Boone–Higman for finitely presented metabelian groups: linear pieces, products, and a mixed-characteristic class

Lane `bh-metabelian-5-3-7`, 2026-09-12. Target: item (7) of Problem 5.3 in
Belk–Bleak–Matucci–Zaremsky (BBMZ), arXiv:2306.16356v3.

**Outcome: Problem 5.3(7) is not settled.** This lane records:
- an exact reduction to products of metabelian linear groups of distinct characteristics;
- a routine but unrecorded class inside the permutational class `B_A`: soluble
  groups linear over finite products of number fields and one-variable function
  fields, mixing characteristics;
- the precise missing inputs;
- a correction to an attribution the first draft made.

## 1. Sources and verification level

| Source | How it was read | Used for |
|---|---|---|
| BBMZ survey, arXiv:2306.16356v3 | extracted PDF text on MSI (`/scratch.global/sauer354/bh-reviewer/2306.16356.txt`) | Problem 5.3(7), footnote 9; no product-closure statement for BH |
| Zaremsky, arXiv:2405.09722 | extracted PDF text on MSI (`bh-reviewer/2405.09722.txt`) | Theorem 1.1 and its proof (envelope `[V_d′(G), V_d′(G)]`), Definition 4.2, Corollary 4.5, Example 4.7, proof of Theorem 1.2 |
| BFFHZ, arXiv:2503.21882v2 | extracted PDF text on MSI (`bh-reviewer/2503.21882.txt`) | Theorem C and its proof, Remark 3.5, product closure of PBH ("[Zarb, Proposition 5.5]") |
| Bux, arXiv:math/0212365, Geom. Topol. 8 (2004) | arXiv TeX source on MSI (`/scratch.global/sauer354/bhmeta/src-math_0212365/2004-15.tex`) | Theorem A; "Chevalley group" there means semisimple |
| Kochloukova–Sidki, arXiv:1710.04745 | arXiv TeX source on MSI (`bhmeta/src-1710.04745/main.tex`) | Theorem A: `PU(m, A)` over `F_p[x^±1, 1/f_i]` is state-closed, and of type `F_n` by Bux |
| arXiv:2509.05798, *Non self-similar metabelian groups* | arXiv TeX source on MSI | known finitely presented self-similar metabelian groups |
| Wehrfritz, Canad. J. Math. 27 (6) (1975), 1355–1360 | PDF downloaded from Cambridge Core on MSI (`bhmeta/wehrfritz1975.pdf`), read page by page | Theorem 1.1, Corollary 1.2, and the quoted statement of Remeslennikov's theorem |
| Remeslennikov, Alg. i Logika 8 (1969), 72–75 | not read; only through Wehrfritz §1 | linearity when the derived subgroup is torsion-free or of exponent `p` |

**Correction during the lane.** The first draft attributed to Remeslennikov an
embedding of every finitely generated metabelian group in `GL_n` over a finite
product of fields.
- *The statement is true, but it is Wehrfritz's.* Wehrfritz's Corollary 1.2
  (1975) says every finite extension of a finitely generated metabelian group of
  characteristic π "is isomorphic to a quasi-linear group of characteristic π".
- *What Remeslennikov proved.* Only the cases where the derived subgroup is
  torsion-free or of exponent `p`. Wehrfritz writes that "Remeslennikov's results
  have a gap which we propose here to fill".
- *What changed.* The node now cites Wehrfritz, read from the PDF, and proves the
  decomposition step directly.

## 2. Why a product step is unavoidable

**Lemma 2.1.** `Z/p wr Z` is linear only in characteristic `p`.
- Suppose `Z/p wr Z <= GL_n(K)` with `char K != p`. An element of order `p` is
  annihilated by the separable polynomial `X^p - 1`, so it is semisimple.
- The base `⊕_Z Z/p` is an infinite commuting family of such elements. So it is
  simultaneously diagonalizable over `Kbar`, and it lies in `(μ_p)^n`, which is
  finite. Contradiction.

**Lemma 2.2.** `Z wr Z` is not linear in positive characteristic.
- Suppose `Z wr Z <= GL_n(K)`, with `char K = p > 0`.
- *Triangularize.* By Kolchin–Mal'cev, a finite-index subgroup `H` is triangular
  over `Kbar`. The diagonal part `δ: H -> (Kbar^x)^n` is a homomorphism whose
  kernel is unipotent. Unipotent elements have `p`-power order in characteristic
  `p`.
- *The base injects.* `H` contains `t^m` for some `m >= 1`, and a nonzero
  subgroup `B'` of the base `B = Z[x^±1]`. Since `B` is torsion-free, `δ` is
  injective on `B'`.
- *Contradiction.* The image of `δ` is abelian, so `δ(t^m b t^-m) = δ(b)`. Hence
  `t^m b t^-m = b` for all `b` in `B'`. But `t^m` acts on `B` as multiplication by
  `x^m`, which fixes no nonzero element.

So `(Z wr Z) x (Z/p wr Z)` is a finitely generated metabelian group that is linear
over no single field. Mixing characteristics is intrinsic to Problem 5.3(7), and
no single-field linear theorem can settle it.

## 3. The exact reduction

`fg-metabelian-groups-embed-in-products-of-coprimary-quotients`:
- *Module structure.* Let `A = G'` and `Q = G/G'`. By Hall, `A` is a finitely
  generated `ZQ`-module.
- *Decomposition.* A primary decomposition `0 = ∩ M_i` gives quotients `G/M_i`
  with `(G/M_i)' = A/M_i` coprimary.
- *Pure pieces.* Each piece is torsion-free, when its associated prime contains no
  nonzero integer, or of `p`-power exponent, when it contains `p`.
- *Linearity.* Torsion-free pieces are linear in characteristic 0 (Remeslennikov,
  as quoted by Wehrfritz). `p`-power pieces are linear in characteristic `p`
  (Wehrfritz, Theorem 1.1).
- *Merging.* Merging pieces of equal characteristic gives
  `G -> G_0 x G_(p_1) x ... x G_(p_s)`, which is Wehrfritz's Corollary 1.2.

BBMZ footnote 9 (Baumslag–Remeslennikov) says every finitely generated
metabelian group embeds in a finitely presented one. So:

> Problem 5.3(7) ⟺ Boone–Higman for all finitely generated metabelian groups
> ⟺ (P),

where (P) is Boone–Higman for every finite product of finitely generated
metabelian linear groups over fields of pairwise distinct characteristics. Its
one-factor cases (M0) and (Mp) are the single-characteristic classes.
- *Forward:* every such product is finitely generated metabelian.
- *Backward:* the embedding of `G` into such a product, above.

The graph route `fp-metabelian-bh-via-linear-factors-and-products` asks for more
than (P) needs: the decomposition, the two general linear roots, and general
product closure.

## 4. Is Boone–Higman closed under direct products?

**Status: open, as far as the sources read show.**
- **BBMZ survey text:** it states no product closure for the Boone–Higman class.
- **BFFHZ:** they state closure under direct products and commensurability only
  for the permutational property. Line 203 of the extracted text reads "PBH is
  stable under commensurability and direct products [Zarb]", and the proof of
  Corollary F cites "[Zarb, Proposition 5.5]".

The claim `boone-higman-closed-under-finite-direct-products` was landed by lane
`bh-product-closure` (36402f028). It carries this lane's attempts, together with:
- the relative-actor product lemma `relative-pbh-closed-under-finite-direct-products`;
- routes through the conjecture and through FFWZ Question 5.9 kernel removal;
- the remark that no nontrivial product is MIF.

This lane adds the route `bh-direct-products-via-mif-envelopes`: if BFFHZ
Question 3.4 has a positive answer, then envelopes enlarge to MIF ones, their
subgroups lie in `B_A` by BFFHZ Theorem C, and `B_A` is closed under products.

## 5. What is settled: soluble groups over global fields, in `B_A`

**5.1. Röver–Nekrashevych groups are highly transitive**
(`rover-nekrashevych-groups-are-highly-transitive`).
- *Known.* BFFHZ Remark 3.5 lists "all finitely presented commutator subgroups of
  Röver–Nekrashevych groups V_n(G) [Nek18, Theorem 4.7]" among the highly
  transitive finitely presented simple groups.
- *The node's independent check:*
  - fullness with respect to cone partitions;
  - matching two `k`-tuples in one orbit, by local sections on deep cones and a
    prefix replacement on the complements, whose cone counts agree mod `d - 1`;
  - passage to nontrivial normal subgroups, by density in `Sym(O)` and
    Schreier–Ulam–Baer.

**5.2. Subgroups of finitely presented self-similar groups lie in `B_A`**
(`fp-self-similar-subgroups-satisfy-permutational-boone-higman`). This is known in
substance.
- Zaremsky's envelope is a finitely presented commutator subgroup of a
  Röver–Nekrashevych group.
- BFFHZ Theorem C puts every subgroup of a highly transitive finitely presented
  simple group in PBH.
- Part (b) reads `Z[1/m]^N x| GL_N(Z[1/m])` off Zaremsky's proof of Theorem 1.2.

**5.3. Function fields** (`function-field-soluble-groups-embed-in-fp-self-similar-groups`).
Let `G <= GL_n(K)` be finitely generated and soluble, with `char K = p` and
`trdeg K <= 1`. Some finite-index subgroup of `G` lies in
`A_S = O_S^n x| B_n(O_S) ≅ PU(n+1, O_S)`, where `O_S` is the ring of S-integers
of a global function field and `|S| >= 3`.
- *Finitely presented:* Bux's Theorem A for the semisimple `SL_(n+1)`, then the
  split extension by `O_S^x`, then the quotient by the scalars.
- *Self-similar:* Zaremsky's Example 4.7, with `J = O_S x_0` for any nonzero
  nonunit `x_0`, and `Γ = B_n(O_S)`.
- *Prior case:* Kochloukova–Sidki Theorem A is the case `K = F_p(x)`,
  `S = {0, ∞, f_1, ..., f_(n-1)}`, with an explicit finite-state automaton. The
  extension here is routine.

**5.4. The class** (`global-field-soluble-linear-products-satisfy-boone-higman`).
Every finitely generated soluble group linear over a finite product of number
fields and positive-characteristic fields of transcendence degree `<= 1` lies in
`B_A`. So it embeds in a finitely presented simple group. Examples inside
Problem 5.3(7):
- Baumslag's `B_p ≅ F_p[x^±1, (1+x)^-1] x| Z^2`, in `A_S` with `n = 1` and
  `S = {0, -1, ∞}`. It was already covered in substance by Kochloukova–Sidki with
  Zaremsky.
- `B_2 x B_3 x BS(1,6)` and all its finitely generated subgroups. `B_2` contains
  `Z/2 wr Z` and `B_3` contains `Z/3 wr Z`, so by Lemma 2.1 the product is linear
  over no single field.

**Relation to the Leavitt result.** `positive-char-surface-linear-groups-satisfy-boone-higman`
already gives Boone–Higman for all single-characteristic linear groups of
transcendence degree at most two, not only soluble ones. It is conditional on
Khanh's unrefereed preprint. For soluble groups of degree at most one, §5 adds:
- an envelope independent of Khanh;
- membership in `B_A`, which is what makes the mixed products work.

**Novelty.** The class of §5.4 is a routine combination of published results. It
was not found written down in the sources of §1. No priority is claimed.

## 6. Precisely what is missing for Problem 5.3(7)

1. **Characteristic zero, positive transcendence degree.**
   - *First case:* Baumslag's torsion-free `B = Z[x^±1, (1+x)^-1] x| Z^2`, linear
     over `Q(x)`. Lane `bh-baumslag-char0-metabelian` (c33366434) records it as
     `baumslag-char-zero-metabelian-group-satisfies-boone-higman`.
   - *The product step cannot help.* `B` is a one-factor case.
   - *Excluded hosts:*
     - `B` itself as a self-similar input (`baumslag-char-zero-metabelian-group-is-not-self-similar`);
     - affine self-similar hosts;
     - Leavitt unit groups over characteristic-zero rings;
     - unit-group hosts of `Q`-algebras with bounded divisibility, whenever the
       embedding keeps a translation unipotent
       (`char-zero-algebra-unit-hosts-exclude-unipotents`).
   - *Not excluded:* a larger finitely presented self-similar overgroup,
     noncommutative coordinate rings, and twisted Brin–Thompson actors built
     directly from the module.
2. **Positive characteristic beyond degree 1 in `B_A`.**
   - *Degree 2:* Leavitt envelopes exist, but they are not known to be highly
     transitive or MIF, so they do not combine with other characteristics.
   - *Degree ≥ 3:* open even alone (coherence of `L_p^(⊗d)`).
   - *Degree 1 is the limit of Example 4.7.* If `R/xR` is finite for a nonzero
     nonunit `x` of a finitely generated domain `R`, then `R` has Krull dimension
     one.
3. **The product step outside `B_A`.** The cheapest test is whether
   `(L_p ⊗ L_p)^x / F_p^x` is MIF, or embeds in a finitely presented simple MIF
   group.

## 7. Nodes from this lane

- **Established:**
  - `fg-metabelian-groups-embed-in-products-of-coprimary-quotients` (+ proof)
  - `principal-ideal-affine-groups-are-self-similar` (+ citation)
  - `function-field-borel-groups-are-fp-for-three-places` (+ citation)
  - `fp-simple-highly-transitive-groups-satisfy-pbh` (+ citation)
  - `rover-nekrashevych-groups-are-highly-transitive` (+ proof)
  - `fp-self-similar-subgroups-satisfy-permutational-boone-higman` (+ proof)
  - `function-field-soluble-groups-embed-in-fp-self-similar-groups` (+ proof)
  - `global-field-soluble-linear-products-satisfy-boone-higman` (+ proof)
- **Open:**
  - `fp-metabelian-groups-satisfy-boone-higman` (root), route `fp-metabelian-bh-via-linear-factors-and-products`
- **Route into a peer claim:**
  - `bh-direct-products-via-mif-envelopes`, into `boone-higman-closed-under-finite-direct-products`
