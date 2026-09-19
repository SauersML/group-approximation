---
rg: 2
id: decidable-host-classes-reduce-to-canonical-kazhdan-groups
kind: claim
title: A class of groups hosts every decidable group iff it hosts the canonical simple Kazhdan groups EL_3 of Cantor crossed-product algebras, so amenable, Haagerup and residually finite host classes are never universal
artifacts:
  - research/artifacts/gq-bh-synth-reductions.md
distinct_from:
  boone-higman-iff-simple-kazhdan-decidable-inputs: that is the special case where the host class is the finitely presented simple groups; this holds for every host class and names one explicit input per decidable group.
  bh-separators-must-omit-nested-decidable-hosts: that is the disproof side, saying what a separating property must omit; this is the proof side, saying what every universal host class must contain.
  local-boone-higman-iff-boone-higman: that is a local-to-global principle for an arbitrary host class; this is a canonical-input principle for an arbitrary host class, and the two can be combined.
---

**ESTABLISHED** (lane proof, elementary given the cited host lemma; not reviewed; no
priority claimed). Synthesis lane bh-synth-reductions.

## The canonical inputs

For a finitely generated group `Γ`:
- let `Δ = C(Γ)` be its half-line overgroup and `L_Γ = Z/2 ≀ Δ`, acting on `2^Δ`
  by shifts and finite flips;
- let `R_Γ = LC(2^Δ, F_2) ⋊ L_Γ`, a finitely generated Cantor crossed-product
  algebra;
- put `H_Γ = EL_3(R_Γ)`.

By `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, `H_Γ` is infinite,
finitely generated, simple and Kazhdan. It contains `Γ`, and `WP(H_Γ) ≤_T WP(Γ)`.

## Theorem 1 (canonical-input principle)

Let `𝒦` be any class of groups, and say `G` *lies in* `𝒦` if `G` embeds in a member of
`𝒦`. The following are equivalent.
- **(a)** Every finitely generated group with solvable word problem lies in `𝒦`.
- **(b)** Every infinite finitely generated simple Kazhdan group with solvable word
  problem lies in `𝒦`.
- **(c)** `H_Γ` lies in `𝒦` for every finitely generated `Γ` with solvable word problem.

*Proof.*
- (a) ⇒ (b), because such groups are finitely generated and decidable.
- (b) ⇒ (c), because `H_Γ` is such a group whenever `WP(Γ)` is solvable.
- (c) ⇒ (a), because `Γ ≤ H_Γ`. `∎`

No closure property of `𝒦` is used.

## Theorem 2 (new equivalent forms)

Apply Theorem 1 to specific classes `𝒦`. In each item, Γ ranges over finitely
generated groups with solvable word problem.
1. **Boone–Higman.** `boone-higman-conjecture` holds iff every `H_Γ` embeds in a
   finitely presented simple group.
2. **Permutational Boone–Higman.** `permutational-boone-higman-conjecture` holds iff
   every `H_Γ` embeds in a finitely presented group with a type (A) action.
3. **Just-infinite form.** Boone–Higman holds iff every `H_Γ` embeds in a finitely
   presented just-infinite group. This combines Theorem 1 with (1) ⟺ (2) of
   `boone-higman-iff-fp-just-infinite-hosts`.
4. **Isolated hosts.** `every-decidable-group-embeds-in-an-isolated-group` (CGP
   Question 4) holds iff every `H_Γ` embeds in an isolated group.
5. **The dynamical gate of the Leavitt route.**
   `decidable-groups-embed-in-fp-groups-with-minimal-free-sft` (P1) holds iff it holds
   for every `H_Γ`. The same is true of `decidable-groups-lie-in-fp-free-minimal-crossed-products`
   (E). The P1 node already notes that it can be restricted to simple Kazhdan inputs; this
   item fixes an explicit family of them.

## Theorem 3 (Kazhdan filter)

Let `𝒫` be a subgroup-closed property of groups such that no infinite finitely
generated simple Kazhdan group has `𝒫`. Then no class of groups with property `𝒫`
hosts every decidable group. More precisely, no member of such a class contains any
`H_Γ` with `Γ` infinite. Properties of this kind include:
- **amenable**, because (T) plus amenability forces finiteness;
- **Haagerup / a-T-menable**, because (T) plus Haagerup forces finiteness;
- **residually finite**, because infinite finitely generated simple groups are not
  residually finite;
- **every Kazhdan subgroup finite**, and **every finitely generated simple subgroup
  residually finite**.

*Proof.* If `H_Γ` embedded in a group with `𝒫`, then `H_Γ` would itself have `𝒫`. `∎`

**Host families it excludes as universal**, each already dead on main for its own
reason and now covered by one lemma:
- Thompson's `F`, `T`, `V`, the Higman–Thompson groups, and every group acting properly
  on a CAT(0) cube complex. These are Haagerup: Farley's cube complexes and Niblo–Reeves,
  both cited, not re-read. This covers Burger–Mozes-type and Wise-type lattice hosts.
- Self-similar, automaton and finitely generated linear hosts, which are residually
  finite. This matches `self-similar-hosts-contain-only-residually-finite-groups`.
- Normal germ extensions of `V` in the BHM Cor. 2.10 regime
  (`normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`), and full groups of
  amenable-orbit actions (`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`).
- Amenable hosts, such as the Juschenko–Monod simple amenable full groups.

**Open, and decisive for Brin–Thompson hosts.** If `nV` (n ≥ 2) had the Haagerup
property, or only finite Kazhdan subgroups (`kazhdan-subgroups-of-brin-thompson-groups-are-finite`),
then no class of subgroups of Brin–Thompson groups would be universal.

**Hosts that pass the filter:**
- full groups of `V`-stabilized free-action groupoids
  (`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`);
- unit groups of Leavitt tensors;
- elementary and Steinberg groups over rings;
- twisted Brin–Thompson groups `SV_Λ` over Kazhdan actors `Λ`.

## Remark: the canonical inputs already sit in Leavitt-tensor units

Put `L = L_(F_2)(1,2)`.
- **The isomorphism.** `L ≅ L^3` as right modules, so `M_3(R_Γ ⊗ L) ≅ R_Γ ⊗ L`.
- **The embedding.** Hence `H_Γ = EL_3(R_Γ) ≤ GL_3(R_Γ ⊗ L) ≅ (R_Γ ⊗ L)^×`.
- **Why the Leavitt route is natural.** The Leavitt-tensor route
  (`boone-higman-via-leavitt-units-of-rigid-sft-overgroups`) is not ad hoc: the canonical
  inputs already live in units of a Leavitt tensor of a Cantor crossed product, over a
  finitely generated but not visibly finitely presented algebra.
- **What is missing.** A finitely presented simple replacement of `R_Γ`, still a Cantor
  crossed product, whose Leavitt tensor has trivial `K_1` and `K_2`. That is exactly premises
  (E) and (K) of that route.

## Lesson for general BH

Every proof of Boone–Higman, whatever its host class, must embed the explicit groups
`EL_3(LC(2^{C(Γ)}, F_2) ⋊ (Z/2 ≀ C(Γ)))`. Host classes that are dynamical in the
Thompson sense (amenable, Haagerup, residually finite, or with only finite Kazhdan
subgroups) are excluded before any finiteness question arises. The algebraic hosts
that contain the canonical inputs, namely Steinberg and Leavitt-tensor unit groups of
Cantor crossed products, form the route to push.
