# Boone--Higman for Out(F_n) and closed-surface mapping class groups

Lane `bh-out-fn-closed-mcg`, swarm 5, 2026-09-12. Target: items (2) and (3) of
Problem 5.3 in Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, in their open
parts. Those parts are mapping class groups of closed surfaces of genus ≥ 3, and
Out(F_n) for n ≥ 3.

Result of this pass:
- nothing famous is settled, and both roots stay OPEN;
- the reason the BFFHZ method stops is pinned to source;
- one elementary equivalence is proved (covering lifts are virtual sections);
- a no-go follows for genus ≥ 4, and the two classes are reduced to precise
  embedding premises.

## 0. Priority check

The arXiv API was queried on MSI on 2026-09-12 with `all:"Boone-Higman"`, sorted
by submission date, 40 results.
- **Newest hit:** 2026-09-01, "On the Self-Similarity of Permutational Wreath
  Products and Their Embedding into Finitely ...".
- **After BFFHZ (March 2025):** Fournier-Facio--Wu--Zaremsky (March 2026) and a
  paper on stabilisers of oligomorphic actions (June 2025).

No hit treats Out(F_n) or closed-surface mapping class groups.

## 1. Sources read

All PDFs were fetched from arxiv.org on MSI and extracted with pypdf into
`/scratch.global/sauer354/bh-outfn-mcg`.

| Source | Version | Used for |
|---|---|---|
| Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ), arXiv:2503.21882 | v2 | Corollary B and its proof, Remark 2.5, the closing paragraph of Section 4 |
| Belk--Bleak--Matucci--Zaremsky survey, arXiv:2306.16356 | v3 | Problem 5.3, Remarks 5.4 and 5.5 |
| Chen--Salter, arXiv:1804.11235 | v1 | Theorem A, Theorem B, definition of virtual splitting |
| Aramayona--Leininger--Souto, arXiv:0811.0841 | v1 | abstract |
| Aramayona--Souto, arXiv:1011.1855 | v1 | abstract |

## 2. Why the BFFHZ method stops

**Closed surfaces.** From the introduction of BFFHZ:

> "For mapping class groups, the conjecture remains open for closed surfaces of
> genus at least three. Note that the Boone–Higman conjecture is known for many
> finitely generated linear groups [Sco84, Zara], but it is an open problem
> whether mapping class groups of closed surfaces of genus at least three are
> linear. The case of genus two is special, thanks to an exceptional
> relationship with braid groups, which is behind both the proof of linearity in
> [BB01] and our proof of the Boone–Higman conjecture for these groups."

The proof of Corollary B, Section 4, goes through four cases.
1. **At least two punctures.** `MCG(Σ, ∗)` embeds in `Aut(π1(Σ)) = Aut(F_n)` by
   Dehn--Nielsen--Baer.
2. **One puncture.** "Σ∗ has a double cover ~Σ, which must have genus 2g − 1 and
   two punctures. [...] each element in L has a unique lift that fixes the two
   punctures in ~Σ. This defines a homomorphism L → MCG(~Σ), which is injective
   by a version of the Birman–Hilden Theorem [ALS09, Corollary 4]."
3. **Boundary.** Cap with twice-punctured disks.
4. **Genus two.** The hyperelliptic involution is central, and the quotient is
   the mapping class group of the six-punctured sphere.

The load-bearing step for one puncture is the canonical lift fixing marked
points. A closed surface has no marked point to pin a lift to. Section 3 below
shows this is not a technicality: in genus ≥ 4 no choice of cover and marked
points can supply one.

**Out(F_n), Remark 2.5.**
- **Garion--Glasner.** The highly transitive action of Out(F_n) on presentations
  modulo Aut(G) needs "a lawless Tarski monster", for which "no finitely
  presented example is known", so "it is unclear whether the stabilizers of such
  actions can ever be finitely generated, and so this does not seem to produce
  type (A) actions for Out(Fn)."
- **Hull--Osin.** Their actions are "built using small cancellation techniques,
  and so it is even less likely that the methods could lead to a type (A) action
  for Out(Fn)."

**Out(F_n) and closed surfaces, closing paragraph of Section 4.**

> "A natural question is whether a similar approach could prove the (P)BH
> conjecture for Out(Fn), and for mapping class groups of closed surfaces. As
> indicated in Remark 2.5, it seems very difficult to find an action of type (A)
> for Out(Fn) itself, so we would want to embed it in some analog of
> AutG(G∗Fn). However, inner automorphisms of Fn do not interact nicely with
> G-automorphisms, so it is not clear whether this is possible. If a version for
> Out(Fn) were possible, it is likely that a similar argument would also cover
> the mapping class group of a closed surface Σ, since this is an index-2
> subgroup of Out(π1(Σ))."

**Concrete form of the interaction failure** (checked here).
- **The action.** `A = Aut_G(G∗F_n)` acts on `X = Hom_G(G∗F_n, G) ≅ G^n` by
  precomposition. An inner automorphism `c_w` of `F_n`, extended by the identity
  on `G`, sends a tuple to its conjugate by `w(g_1, ..., g_n)`.
- **The quotient.** The quotient of `X` by diagonal conjugation would kill
  `Inn(F_n)`.
- **What breaks.** An `α ∈ A` whose words `α(x_i)` carry constants from `G`
  commutes with diagonal conjugation only if those constants commute with all
  of `G`. For centreless `G`, that leaves only `Aut(F_n)`. So the quotient
  action loses exactly the constant moves that make `A` highly transitive.

**Survey.**
- **Remark 5.4:** "Item (2) remains open for mapping class groups of closed
  surfaces of genus 3 or greater, item (3) remains open for Out(Fn) for all
  n ≥ 3".
- **Remark 5.5:** the route through PIP homeomorphisms of the Thurston boundary
  "would yield a natural Boone–Higman embedding for mapping class groups of
  closed surfaces" if those groups are finitely presented simple. Thurston's
  finite-generation question "remains open".

## 3. Covering lifts are virtual sections

Node: `outer-covering-lifts-are-virtual-sections`. Proof:
`outer-covering-lifts-virtual-sections-proof`.

**(i) Algebraic form.**
- **Setting.** `N` has unique roots, `H ≤ N` has finite index, and `L ≤ Out(N)`.
  A homomorphism `λ: L → Aut(H)` is given such that each `λ(f)` extends to a
  representative of `f`.
- **Conclusion.** The extension is unique, and `f ↦ extension` splits
  `Aut(N) → Out(N)` over `L`.
- **Proof.** Uniqueness: `γ^k ∈ H` for some `k ≥ 1`, then take roots.
  Homomorphism: by uniqueness.

**(ii) Topological form, closed Σ of genus ≥ 2.**
- **Hypothesis.** A homomorphism `λ: L → Mod(Σ̃, P)` for a finite cover
  `Σ̃ → Σ` with nonempty finite `P`, whose values are represented by lifts of
  representatives.
- **Conclusion.** It yields a section of `Mod(Σ, x) → Mod(Σ)` over the kernel of
  the action on `P`.
- **Proof.** A lift fixing `p̃` descends to a representative fixing `x = π(p̃)`.
  Its induced automorphism is determined by (i), so its class in `Mod(Σ, x)` is
  determined by based Dehn--Nielsen--Baer.
- **Converse.** Use the trivial cover.

**Consequences.**
- **Genus ≥ 4.** No such `λ` exists, injective or not, for any finite unbranched
  cover (`closed-mcgs-have-no-covering-lift-to-marked-covers`, from Chen--Salter
  Theorem A: "For g ≥ 4, the Birman exact sequence does not virtually split").
  So `closed-mcg-bh-via-covering-lift-to-marked-cover` is dead.
- **Genus 3.** The BFFHZ-type covering construction exists iff the genus-3 Birman
  sequence splits over a finite-index subgroup. If it does,
  `Mod(S_3) ∈ B_A`, through `punctured-surface-mcgs-satisfy-permutational-boone-higman`
  and closure under finite-index overgroups. Chen--Salter's Theorem A does not
  cover genus 3.
- **Out(F_n).** Lifting to automorphisms of any finite-index subgroup of `F_n` is
  the same as a virtual section of `Aut(F_n) → Out(F_n)`. Such a section would
  give the premise `out-free-groups-virtually-embed-in-aut-free-groups` with
  `m = n`, hence Boone--Higman for `Out(F_n)`. In rank two the section exists,
  because `GL_2(Z)` is virtually free.

**Restricting to a characteristic subgroup gives Out-to-Out maps only.**
- **Out-level embedding.** Let `K ≤ F_n` be characteristic of finite index.
  Restriction gives an injection `Aut(F_n)/K → Out(K)`. Its kernel consists of
  the inner automorphisms by `K`, by uniqueness in (i).
- **Finite extension.** `Aut(F_n)/K` is an extension of `Out(F_n)` by the finite
  group `F_n/K`. Splitting this extension embeds `Out(F_n)` in `Out(K)`, a free
  group of larger rank.
- **Aut-level embedding.** Landing in `Aut(K)` is again a virtual section of
  `Aut(F_n) → Out(F_n)`.

## 4. Region landed in Cairn

Roots, both OPEN:
- `closed-surface-mapping-class-groups-satisfy-boone-higman`
- `out-free-groups-satisfy-boone-higman`

Imports, ESTABLISHED:
- `birman-exact-sequence-does-not-virtually-split` (Chen--Salter Theorem A),
  route `birman-sequence-no-virtual-splitting-citation`
- `punctured-surface-mcgs-satisfy-permutational-boone-higman` (BFFHZ Corollary B
  with its proof), route `punctured-surface-mcgs-pbh-citation`

Derived, ESTABLISHED:
- `outer-covering-lifts-are-virtual-sections`, route
  `outer-covering-lifts-virtual-sections-proof`
- `closed-mcgs-have-no-covering-lift-to-marked-covers` (genus ≥ 4), route
  `closed-mcg-covering-lift-no-go-proof`; it invalidates
  `closed-mcg-bh-via-covering-lift-to-marked-cover`

Sufficient routes with open premises:
- `closed-mcg-bh-via-punctured-mcg-host`, requiring
  `closed-mcgs-virtually-embed-in-punctured-mcgs`
- `out-fn-bh-via-virtual-embedding-in-aut-fn`, requiring
  `out-free-groups-virtually-embed-in-aut-free-groups`

## 5. What an attack now has to do

1. **Genus three.** Decide whether the genus-3 Birman exact sequence splits over
   a finite-index subgroup of `Mod(S_3)`. A section settles Boone--Higman for
   `Mod(S_3)`. Non-splitting kills the covering template in genus 3 as well.
   Luo--Watanabe, arXiv:2502.14343v2 (abstract, read from the PDF on MSI), prove
   that the profinite Birman sequence does not split over finite-index
   subgroups containing the Johnson subgroup, in genus ≥ 3. This pass did not
   check whether that excludes discrete sections over arbitrary finite-index
   subgroups.
2. **Out(F_n), n ≥ 3.** Decide whether `Aut(F_n) → Out(F_n)` splits over a
   finite-index subgroup. A section settles Boone--Higman for `Out(F_n)`.
3. **Non-covering embeddings.** Embed a finite-index subgroup of `Mod(S_g)` in a
   punctured mapping class group of genus ≥ 2g, or of `Out(F_n)` in some
   `Aut(F_m)`, by a construction that is not a lift. Aramayona--Souto rule out
   targets of genus ≤ 2g − 1 for the full group when g ≥ 6: every nontrivial
   homomorphism is "induced by an embedding".
4. **A type (A) host containing Out(F_n)** that is not of the form
   `Aut_G(G∗F_n)`. BFFHZ's Question-level open problem.

## 6. Not claimed

- **Novelty.** None for the lemma of Section 3, which is elementary; it is
  recorded because it turns a vague obstacle into two sharp questions.
- **Branched covers.** Not analysed.
- **Unverified here.** No statement on linearity of `Out(F_n)`. No statement on
  the literature status of virtual splitting of `Aut(F_n) → Out(F_n)` for
  n ≥ 3 beyond the search recorded in the premise node.
- **Lean.** No Lean counterpart.
