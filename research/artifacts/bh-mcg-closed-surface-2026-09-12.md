# Boone--Higman for closed-surface mapping class groups: hosts and obstructions (2026-09-12)

**Lane:** bh-mcg-closed-surface.

**Target:** `closed-surface-mapping-class-groups-satisfy-boone-higman`, which
asks whether `Mod(S_g)`, `g ≥ 3`, embeds in a finitely presented simple group.

## 1. Live embedding premises

At main d71ae9349 the only live embedding premise is
`closed-mcgs-virtually-embed-in-punctured-mcgs`. It is consumed by route
`closed-mcg-bh-via-punctured-mcg-host`, together with:
- `punctured-surface-mcgs-satisfy-permutational-boone-higman`, which imports BFFHZ
  Corollary B;
- `boone-higman-type-a-class-closed-under-finite-extensions`.

The Birman-sequence inputs are:
- `birman-exact-sequence-does-not-virtually-split`: Chen--Salter Theorem A,
  `g ≥ 4`;
- `birman-sequence-genus-three-does-not-virtually-split`: on main, reviewed PASS.

## 2. Literature status

Belk--Bleak--Matucci--Zaremsky, survey arXiv:2306.16356v3, Remark 5.4, verbatim:
"Item (2) remains open for mapping class groups of closed surfaces of genus 3 or
greater". The arXiv search listing for "Boone-Higman", read on MSI through the
newest entry 2609.01868, shows no closed-surface result. The case stays OPEN.

## 3. Landed in this lane

| node | kind | commit | content |
|---|---|---|---|
| `cantor-punctured-birman-sections-have-no-finite-end-orbit` | claim | 25d2ad26e | a section of `Mod(Σ, E) → Mod(Σ)` over a finite-index subgroup has no finite orbit on `E` |
| `cantor-punctured-birman-section-orbit-proof` | route | 25d2ad26e | a finite orbit gives a finite-index point stabilizer; forgetting `E ∖ {x}` splits the Birman sequence over it |
| `closed-mcg-pair-orbit-finite-actions-have-large-stabilizers` | claim | 25d2ad26e | with finitely many pair orbits, stabilizers on infinite orbits are not finite, not normal, fix no multicurve and are not virtually cyclic |
| `closed-mcg-pair-orbit-stabilizer-proof` | route | 25d2ad26e | bi-invariant intersection numbers `i(M, fM)` and `i(λ+, fλ+)·i(λ−, fλ−)` grow along twist powers |
| `aramayona-funar-asymptotic-mcgs-are-fp-extensions-of-v` | claim | 5ab862d68 | literature import: AF exact sequences, finite presentation and perfection; ABFPW type `F∞` |
| `aramayona-funar-asymptotic-mcg-citation` | route | 5ab862d68 | the pages read and the items quoted |
| `closed-mcg-finite-index-subgroups-do-not-embed-in-v` | claim | a93479570 | no finite-index subgroup of `Mod(S_g)`, `g ≥ 2`, embeds in `V` |
| `closed-mcg-v-nonembedding-via-koberda` | route | a93479570 | large powers of three twists give `Z² ∗ Z` (Koberda Theorem 1.1), and `V` has no such subgroup (survey Theorem 4.6(1)) |
| `closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v` | claim | b935df3a5 | finite image in `V` gives the punctured premise; otherwise the image is infinite and the kernel nontrivial; normal subgroups and simple quotients of the hosts |
| `closed-mcg-asymptotic-host-dichotomy-proof` | route | b935df3a5 | finitely many compactly supported classes fit in one bordered genus-`h` subsurface; `V` is simple |

The same commit as this revision adds Attempts 6 and 7 to the root and
Attempt 4 to the premise.

### 3a. The finite-orbit obstruction

`E ⊂ Σ` is closed and totally disconnected, and `σ: L → Mod(Σ, E)` satisfies
`F∘σ = id_L`. If `x` had a finite orbit, then `L_x` would have finite index, and
restricting to classes fixing `x` gives `Mod(Σ, x)`. So the Birman sequence would
split over `L_x`, which Chen--Salter and the genus-3 claim exclude. Injectivity
of `σ` is not used.

**Consequence for hosts.** Suppose a host acts on a Cantor set of ends through
a Higman--Thompson group `V`, and contains `Mod(Σ)` through a forgetful section.
Then the image of `Mod(Σ)` in `V` has no finite orbit, so it is infinite.

### 3b. Type (A) self-actions

A type (A) action of a finite-index subgroup `G ≤ Mod(Σ)` would settle the target
through `type-a-action-gives-boone-higman-for-subgroups` and the finite-extension
closure. The pair clause kills every action whose stabilizers:
- are finite or normal;
- fix a multicurve (so curves, multicurves, and curve- or pants-graph vertices
  are out);
- are virtually cyclic.

**What is not decided.**
- Hull--Osin highly transitive actions, not re-read in this pass, satisfy the
  pair clause. So any obstruction must use finite generation of stabilizers.
- Actors that properly contain `Mod(Σ)`.

### 3c. No finite-index subgroup embeds in `V`

Let `g ≥ 2` and let `L ≤ Mod(S_g)` have finite index.
- Take meridians `a` and `b` of two handles, and a curve `c` meeting each once.
- The twists `T_a, T_b, T_c` are irredundant. Their coincidence correspondence
  is one edge plus an isolated vertex.
- By Koberda Theorem 1.1, large powers generate `Z² ∗ Z`, and taking the powers
  divisible by `[Mod(S_g) : L]!` puts them in `L`.
- Survey Theorem 4.6(1), page 11 (Bleak--Salazar-Díaz 2013): `Z² ∗ Z` does not
  embed in `V`.

So every homomorphism `L → V` has nontrivial kernel.

### 3d. Copies inside the Aramayona--Funar groups

Let `ρ: L → G` be injective, with `G = B_h` or `H_h`, `π: G → V` the quotient,
and `K = ker(π∘ρ)`.
- **Finite image in `V`.** `K` is finitely generated, of finite index, and lands
  in `PMod_c(Σ_h)`. Its generators are supported in one compact genus-`h`
  subsurface `S ≅ S_{h,n}`, each of whose complementary components is noncompact
  with one boundary circle.
  - Extending by the identity embeds `Mod(S)` in `PMod_c`.
  - Capping with twice-punctured disks gives `K ↪ Mod(S_h^{2n})`, which is the
    premise.
- **Infinite image in `V`.** Then `K ≠ 1`, by 3c. Nothing here excludes this
  case.
- **Normal subgroups and quotients.**
  - Every normal subgroup of `G` lies in `PMod_c` or supplements it.
  - `G` is not simple.
  - A simple quotient containing `L` is generated by the image of `PMod_c`.
- **Forgetful sections** (`h = g`) have infinite image in `V`, by 3a, since
  `PMod_c` fixes every end.

The inclusion input, AF Lemma 2.1 read as "extension by the identity is
injective", is the infinite-type analogue of Farb--Margalit Theorem 3.18. It is
not re-proved.

## 4. Host candidates

**What was read.** The PDFs were fetched on MSI and read page by page with the
image reader:
- AF arXiv:1701.08132v2, pages 1--12;
- ABFPW arXiv:2110.05318v5, pages 1--5;
- Koberda arXiv:1007.1118v4, pages 2--3;
- survey arXiv:2306.16356v3, pages 11--14.

Fetched but not read in this pass: 2010.07225, 2001.04579, 2405.18354,
2603.24687, 2506.02319, 2605.20564.

| candidate | contains a finite-index `L ≤ Mod(S_g)`? | finitely presented? | normal subgroups |
|---|---|---|---|
| AF `B_h`, `H_h`, `h ≥ 0` | not stated in any source read; finite image in `V` reduces to the premise, and forgetful sections have infinite image | yes, AF Theorem 1.2; `F∞`, ABFPW Theorem 1.1 | `PMod_c(Σ_h)` with quotient `V`; every normal subgroup lies in `PMod_c` or supplements it; not simple |
| Funar--Kapoudjian `B_0` | same as `B_0` of AF, by the ABFPW identification `B_{2,1}(S², S²)` | yes | as above with `h = 0` |
| Funar--Kapoudjian `B_∞` | not stated; contains the mapping class group of every compact surface with nonempty boundary (ABFPW page 2, citing [26, Theorem 3.1]) | `F∞`, ABFPW Theorem 1.1 | sequence (1.3) with quotient `V_{2,1}`; the dichotomy was not checked |
| ABFPW `B_{d,r}(O, Y)` | not stated | `F∞`, ABFPW Theorem 1.7 | sequence (1.3) with quotient `V_{d,r}`; the dichotomy was not checked |
| commutator subgroup of `B_h`, `H_h` | equals the host for `h ≥ 3`, AF Corollary 1.5 | yes | same as the host |
| simple quotient of `B_h`, `H_h` | only if the image of `PMod_c` is the whole quotient | not studied | simple |
| Thompson's `V` | no, by 3c | yes | simple |
| twisted Brin--Thompson `SV_Γ` | yes, if some finite-index subgroup has a type (A) action | yes, under the hypotheses | simple |

**Further facts about `B_h` and `H_h`.**
- AF Theorem 1.11: every homomorphism from a higher-rank lattice to them has
  finite image.
- AF Theorem 1.13: they are not linear.
- AF Lemma 2.1: they contain `Mod(S_{h,n})` for `n ≥ 1`.

### Twisted Brin--Thompson hypotheses

Survey Theorem 4.15, page 14: "Let G be a group acting faithfully on a set S.
Suppose that G is finitely presented, the stabilizer of each point in S is
finitely generated, and the action of G on S has finitely many orbits of pairs.
Then G embeds as a subgroup of a finitely presented simple group, namely the
twisted Brin–Thompson group SV_G."

**Natural actions of finite-index subgroups.** Each fails, by
`closed-mcg-pair-orbit-finite-actions-have-large-stabilizers` or directly:
- **Translation on itself.** The stabilizers are trivial, and the survey notes
  that this action never has finitely many orbits of pairs for an infinite
  group.
- **Curves, multicurves, pants decompositions.** The stabilizers fix a
  multicurve.
- **Cosets of a finite or normal subgroup, or a virtually cyclic one.**
  Excluded by the claim.

**Not decided.**
- Actions with large, finitely generated stabilizers.
- Type (A) actions of groups that properly contain `Mod(Σ)`, including `B_h`
  and `H_h` themselves. Their action on the Cantor set is not faithful, since
  `PMod_c` acts trivially.

## 5. Status

`closed-surface-mapping-class-groups-satisfy-boone-higman` and
`boone-higman-conjecture` remain OPEN. Nothing here proves an embedding.

The landed claims are four exact obstructions or reductions:
- forgetful sections into Cantor-punctured hosts have infinite image in `V`;
- type (A) actions need large stabilizers;
- no finite-index subgroup embeds in `V`;
- copies in the Aramayona--Funar groups either give the punctured premise or
  have infinite image in `V`.

The one open case left by this lane's host analysis is an injective
homomorphism from a finite-index subgroup to `B_h` or `H_h` with infinite image
in `V`.
