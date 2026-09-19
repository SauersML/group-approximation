---
rg: 2
id: cover-pair-failures-have-finite-partial-table-witnesses
kind: claim
title: A failure of CP, of CP_col or of NPE is witnessed by a finite partial multiplication table, so each of the three is local, marked-closed, colimit-closed and testable at one fixed finitely presented group
distinct_from:
  absorbing-marked-groups-form-an-open-set: that proves openness for absorptions, whose data are identities of one translation lift; this proves it for strongly post-surjective covers of SFT domains, where post-surjectivity quantifies over all configurations and needs a compactness step to become finite.
  gottschalk-surjunctivity-fixed-two-generator-tester: that is the fixed-host reduction for surjunctivity, whose failure is an injective non-surjective automaton; this is the same reduction for CP, CP_col and NPE, whose failures are strongly post-surjective covers.
  universal-all-group-subgroup-colimit-class-tester: that is the abstract tester for any class closed under subgroups and directed colimits; this proves that the classes of groups satisfying CP, CP_col or NPE have those two closure properties.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the open statement CP; this proves only that CP, and its conjuncts, are local properties of groups.
  local-approximation-properties-are-marked-closed: that is marked closedness for metric table-approximation properties; this is marked closedness for three symbolic-dynamical rigidity properties that are not of that form.
---

**ESTABLISHED (elementary)** by [[cover-pair-failures-have-finite-partial-table-witnesses-proof]].

**Notation.**
- A *cover pair* over a group `G` is a subshift of finite type `X ⊆ A^G` together with an automaton
  `F : X → A^G` that is strongly post-surjective with lifts in `X`. That means there is a finite `Φ ⊆ G` such
  that, for every `x ∈ X` and every `z ~ F(x)`, some `x' ∈ X` with `x' ~ x` has `F(x') = z` and
  `Δ(x, x') ⊆ Δ(F(x), z)Φ`.
- `CP(G)` says that no cover pair over `G` has `X ≠ A^G` and a constant configuration in `X`. This is
  `constant-point-sft-domains-admit-no-post-surjective-covers` at `G`.
- `CP_col(G)` says that no such cover pair collides at every constant. *Colliding at a constant* `c^G ∈ X` means
  that two distinct `x, y ∈ X`, each asymptotic to `c^G`, have `F(x) = F(y)`.
  `CP(G) ⟺ Gottschalk(G) ∧ CP_col(G)` by the w15 split recorded on the CP claim.
- `NPE(G)` says that no automaton `A^G → B^G` with `|B| > |A|` is strongly post-surjective. This is
  `post-surjective-automata-never-enlarge-the-alphabet` at `G`.
- A *partial embedding* of a finite set `K ⊆ G` into a group `G'` is an injective map `ψ : K → G'` with
  `ψ(ab) = ψ(a)ψ(b)` whenever `a, b, ab ∈ K`.

**Theorem L (finite witnesses).** Let `P` be one of `CP`, `CP_col`, `NPE`, and suppose `P(G)` fails. Then there is
a finite `K ⊆ G` with `1 ∈ K` such that `P(G')` fails for every group `G'` that admits a partial embedding of `K`.
- The witness in `G'` uses the same alphabet, the same forbidden patterns, the same local rule and the lift
  constant `ψ(Φ)`, all transported along `ψ`.
- The only non-local ingredient, global admissibility of finite patterns in `X`, is replaced by admissibility
  inside one finite set `L ⊆ K`. The set `L` is chosen by compactness.

**Corollaries.** Let `P` be `CP`, `CP_col` or `NPE`.
1. **Local and hereditary.** `P(G)` holds iff `P(H)` holds for every finitely generated `H ≤ G`. If `P` fails at
   `H ≤ G`, then it fails at `G`.
2. **Closed.** The groups satisfying `P` are closed under subgroups, under directed colimits with arbitrary
   structure maps, and under local embeddability: if every group in a class `C` satisfies `P`, then so does every
   group that is locally embeddable into `C`. In the space of marked groups, the marked groups satisfying `P`
   form a closed set, and failure of `P` is an open condition.
3. **Finitely presented witnesses.** If `P` fails at some group, it fails at some finitely presented group.
4. **One fixed tester.** Let `U` be the two-generator finitely presented group of
   `universal-all-group-subgroup-colimit-class-tester`. Then `P` holds for every group iff `P(U)` holds. The
   same `U` also tests Gottschalk (`gottschalk-surjunctivity-fixed-two-generator-tester`). So
   `constant-point-sft-domains-admit-no-post-surjective-covers`, read over all groups, is equivalent to
   `Gottschalk(U) ∧ CP_col(U)`. All three are statements about one fixed group.
5. **Soficity-free base case.** Finite groups satisfy `CP` and `NPE` by counting. So every LEF group, and in
   particular every residually finite group, satisfies `CP`, `CP_col` and `NPE` by Corollary 2 and
   `residually-finite-groups-are-lef`. This does not use soficity.

**What this changes.**
- Every question about CP, and about its only non-Gottschalk content `CP_col`, can now be moved freely:
  - to finitely generated or finitely presented groups;
  - along marked limits and local embeddings;
  - to one fixed host.
  Before this, only Gottschalk and dual surjunctivity had these closure properties in the graph.
- A counterexample at a group `G` persists at every group into which a large enough finite piece of `G` embeds
  partially. This is consistent with the w13 host-change kill on the CP claim: failures move to every
  overgroup, but sections never appear.
- The companion claim `cp-failures-transfer-between-hyperbolic-and-leh-groups` uses this to reduce CP at
  limits of hyperbolic groups to hyperbolic quotients of one Kazhdan group. It also names the universal sentence
  at which every transfer from hyperbolic or finite models dies before reaching `U`.
