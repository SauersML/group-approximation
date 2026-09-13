# solve-bh-free-solvable (2026-09-13)

Lane `solve-bh-free-solvable`. Target: Boone--Higman for finitely generated solvable
groups beyond metabelian, starting with free solvable groups `S_(r,d)`, `d >= 3`.

## 1. Outcome

Established in Cairn, not independently reviewed:

| node | content |
|---|---|
| `type-a-actors-closed-under-type-a-lamp-wreaths` | `Λ wr_S Γ` on `S × Y` is of type (A) when `Λ` on `Y` and `Γ` on `S` are |
| `pbh-groups-act-freely-in-relative-automorphism-actors` | every `G ∈ B_A` acts freely, with infinitely many orbits, on BFFHZ's actor set `Hom_M(M * F_2, M)` |
| `permutational-boone-higman-closed-under-wreath-products` | `A, G ∈ B_A` ⟹ `A wr_X G ∈ B_A` when `X` is countable with finite stabilizers; in particular `A wr G` |
| `magnus-embedding-f-over-n-prime-into-wreath-product` | literature import: `F/[N,N] ≤ Z^r wr F/N` |
| `free-solvable-groups-satisfy-permutational-boone-higman` | `F/N ∈ B_A` ⟹ `F/N^(d) ∈ B_A`; all free solvable groups are in `B_A` |

OPEN: `pbh-closed-under-permutational-wreaths-with-infinite-stabilizers`.

## 2. The mechanism in one paragraph

A regular wreath product needs a free orbit of the top group inside an actor. BFFHZ
Theorem C puts any `G ∈ B_A` inside a finitely presented simple MIF group `M`. Their
Theorem E gives `Aut_M(M * F_2)` a type (A) action on `Hom_M(M * F_2, M) ≅ M^2`. The
translations `x_1 -> x_1 g`, which BFFHZ use to embed `M`, act by right multiplication
on the first coordinate, so they act freely. Placing a type (A) actor containing the
lamps at every point, the wreath product `Λ wr_S Γ` acts on `S × Y` with type (A),
by Cornulier's criterion plus a check of the other clauses. Magnus's embedding
`F/[N,N] ≤ Z^r wr F/N` then climbs the derived series.

## 3. Sources read (all on MSI, 2026-09-13)

Extracted text of BFFHZ arXiv:2503.21882v2 in
`/scratch.global/sauer354/bh-reviewer/`; arXiv TeX sources in
`/scratch.global/sauer354/solve-bh-free-solvable/`.

- **BFFHZ arXiv:2503.21882v2.**
  - l.97: the only "wreath" occurrence, `V wr_S Γ` in the definition of `SV_Γ`.
  - l.114--116: `Hom_G(G∗F_n; G)` is in bijection with `n`-tuples, and the action is
    by precomposition.
  - l.120--126: the definition of type (A).
  - l.195--198: Theorem E.
  - l.205--207: Corollary F (free products).
  - l.349--350: "(right) action ... by precomposition".
  - l.360--362: the definition of MIF.
  - l.640--647: the proof of Theorem E.
  - l.651--653: `V` is a finitely presented simple MIF group.
  - l.661--663: the embedding `g -> (x_1 -> x_1 g, x_2 -> x_2)`.
- **Zaremsky arXiv:2405.18354** (TeX `fin_pres_twistedBT.tex`).
  - l.126: Cornulier's criterion restated.
  - l.510--532: Propositions 5.5 and 5.6.
  - l.534--536: Question 5.7 ("What about wreath products? Or general semidirect
    products?").
  - l.28--47: the preamble shows that `question` shares the theorem counter.
- **Myasnikov--Roman'kov--Ushakov--Vershik arXiv:0807.1032** (TeX `freesol_WP_30.tex`).
  - l.268--276: definition of `S_(r,d)`.
  - l.278--308: the Magnus embedding and `M(G) = A_r wr G`.
  - l.385--414: Fox's theorem.
- **BBMZ survey arXiv:2306.16356v3** (extracted text).
  - Near l.888: Problem 5.3, items (1)--(13).
  - l.907ff: footnote 9, on derived length three.
- **arXiv:2609.01868** (Almeida, Dantas, Oliveira-Tosti; TeX `main.tex`).
  - l.86: the abstract.
  - l.160--236: `Z^d wr_X G` for contracting `G`, and their questions.
- **Fournier-Facio--Kropholler--Lyman--Zaremsky arXiv:2506.02319** (TeX
  `oligomorphic.tex`).
  - l.396--446: the Boone--Higman section, on Burger--Mozes actors only; no
    permanence statement.
- **Fournier-Facio--Wu--Zaremsky arXiv:2603.24687** (extracted text).
  - l.585--600: Lemma 3.1, relative simplicity of wreath products; not permanence.
- **Cornulier arXiv:math/0509090**: taken as pinned by
  `bh-type-a-lamp-wreath-closure-proof` (TeX l.147--157). Not re-read here.
- **Magnus 1939**: primary source not read; imported through MRUV.

## 4. Novelty search (bounded)

- **Web searches.**
  - "permutational Boone-Higman wreath product type (A) closed under wreath products";
  - "permutational Boone-Higman conjecture wreath products type (A) 2026 arXiv
    permanence semidirect".
- **What turned up.** The papers above, and a Glasgow eprint of a survey, "Progress
  around the Boone--Higman conjecture". Its PDF could not be text-extracted on MSI
  (no `pdftotext`), so it was **not** checked.
- **Result.** Neither closure of the permutational class under wreath products nor
  Boone--Higman for free solvable groups of class `>= 3` was found printed. Zaremsky
  still lists wreath products as open in Question 5.7 (TeX timestamp November 2024).
  BFFHZ v2 (April 2025) answer only free products.
- **Credit.** No priority is claimed beyond this search.

## 5. Exact remaining gaps

1. **Infinite stabilizers.** Take `G`-sets `X` with infinite point stabilizers that
   are not type (A) sets of `G`, e.g. `Z wr_(F_2/⟨a⟩) F_2`. Recorded as OPEN.
2. **General semidirect products** `N ⋊ G` with `N, G ∈ B_A` (Zaremsky Question 5.7,
   last clause). Untouched.
3. **Whether `A wr G` itself admits an action of type (A)** (the literal form of
   Question 5.7). Untouched.
4. **Solvable groups with solvable word problem not of the form `F/[N,N]`** over a
   `B_A` quotient, such as free centre-by-metabelian groups. Untouched.
5. **Non-linearity of `S_(r,3)`.** Expected by Mal'cev's theorem; not proved here.
