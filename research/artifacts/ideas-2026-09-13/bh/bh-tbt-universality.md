# Idea lane bh-tbt-universality (2026-09-13)

Target: `boone-higman-conjecture`. Lens: twisted Brin--Thompson universality.
This is an ideas file, not a claim. Nothing here is established, and no node was edited.

## Starting point (read on origin/main 991380d00)

- `type-a-action-gives-boone-higman-for-subgroups`, from Zaremsky arXiv:2405.18354, verbatim there:
  - SV_G is finitely presented iff the action is of type (A): faithful, G finitely presented, point stabilizers finitely generated, finitely many orbits of 2-element subsets;
  - every subgroup of a type (A) actor satisfies BH.
- `fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ Theorem C): PBH ⇔ embedding in an fp simple highly transitive group ⇔ embedding in an fp simple MIF group.
- Obstructions already on main, which none of the approaches below may repeat:
  - `complexity-bounded-host-classes-are-not-universal`: no host class with one recursive time bound is universal.
  - `relative-automorphism-fp-host-reflects-base-presentation`: the universal computable-core upgrade fails.
  - `shell-finite-biindex-hosts-require-large-intersections`: almost malnormal hosts fail.
  - `normalizer-image-of-type-a-actor-is-type-a`: known actors have small permutation normalizers.
- arXiv:2506.02319, Fournier-Facio–Kropholler–Lyman–Zaremsky, abstract checked. For groups of finite virtual cohomological dimension and all countable linear groups, every oligomorphic action on an infinite set has a finite subset whose stabilizer is not of type FP∞. This obstructs FP∞ finiteness of twisted Brin–Thompson hosts. It does not obstruct type (A), which asks only for finitely generated point stabilizers and finitely many orbits on 2-subsets.

## Approach 1. Commensurated actors (Schlichting completion lens)

**Idea.**
- Embed a decidable G in a finitely presented Γ that has a finitely generated, core-free, *commensurated* subgroup H of finite bi-index. Then Γ ↷ Γ/H is type (A).
- The Schlichting completion is then a totally disconnected locally compact group with a compact open stabilizer, acting on locally finite orbital graphs. Lattice and tree machinery could then build universal hosts.

**Would prove.** PBH, and hence BH, for every input of such hosts.

**Kill test (hand computation, done).**
- Finite bi-index means Γ = H g_1 H ∪ … ∪ H g_k H.
- The suborbit H g_i H / H has size [H : H ∩ g_i H g_i⁻¹], which is finite when H is commensurated.
- So Γ/H is a finite union of finite sets.

**Verdict: KILLED.** Commensurated plus finite bi-index forces finite index.

**By-product.**
- Every type (A) action on an infinite set has a point stabilizer with an infinite suborbit.
- Equivalently, some orbital graph has infinite valency.
- So hosts from tdlc groups or locally finite graphs can only enter by acting on a *different* set: boundaries, clopen sets, and similar.

## Approach 2. One actor with a universal permutation normalizer

**Idea.**
- Find a single finitely presented type (A) actor Γ ≤ Sym(S) whose normalizer N in Sym(S) satisfies: for every finitely generated G with solvable word problem, N contains a finitely presented Q ⊇ G with Q ∩ Γ = 1.
- `normalizer-image-of-type-a-actor-is-type-a` then makes ΓQ a type (A) actor, so G satisfies PBH and BH.
- Q can be Clapham's finitely presented overgroup with solvable word problem. It is recorded in A.4 of `research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md` and was not re-read here.
- Why this could dodge the complexity principle: the principle constrains the hosts ΓQ, which vary with Q. One fixed Γ may have bounded complexity while its uncountable normalizer has finitely generated subgroups of unbounded complexity.

**Would prove.** BH reduces to universality of *one* normalizer, not of a class of actors.

**Kill tests run.**
- **Thompson V on dyadics.** Its normalizer is Aut(V) (Rubin). Per the repo node, Aut(V) consists of rational homeomorphisms, which have exponential word problem, so it is not universal. Source not re-read.
- **Houghton actors.** The normalizer is expected to be commensurable with the actor. The repo notes this but does not write it out.
- **SV_W on clopen sets.** Coordinate permutations only move the question back to W, so this is circular.
- **Hand check.** Γ ⊇ FSym(S) imposes no restriction by itself, since N(FSym(S)) = Sym(S). The restriction comes from the quotient Γ/FSym(S), for example the eventual-translation structure of Houghton groups.

**Verdict: SURVIVES** as a sharper reformulation. No candidate actor yet.

**Next test.** Compute the permutation normalizers of Brin–Thompson nV on dyadic points, and of finitely presented full Cantor groups that are not rational (see `fp-full-binary-cantor-groups-have-type-a-actions`). Look for any finitely generated subgroup above exponential word-problem complexity.

## Approach 3. Finitary-by-input actors (coarse Houghton lens)

**Idea.**
- For a decidable G acting on X (regular, or on cosets), put Γ = Alt_fin(X) ⋊ G.
- Γ contains Alt_fin(X), so it is highly transitive on X, with one orbit on 2-subsets.
- Point stabilizers contain Alt_fin(X∖{x}) ⋊ Stab_G(x).
- If Γ were finitely presented with finitely generated stabilizers, Γ ↷ X would be type (A) and G ≤ Γ would satisfy PBH.

**Would prove.** PBH for every G admitting such a finitely presented finitary extension.

**Kill test (literature, abstract checked).**
- Cornulier, arXiv:math/0509090: a permutational wreath product W^(X) ⋊ G is finitely presented iff G and W are finitely presented, G acts on X with finitely generated stabilizers, and G has finitely many orbits on X².
- If the finitary alternating analogue holds, then finite presentation of Alt_fin(X) ⋊ G needs G ↷ X to be type [A_2] already, which is circular. That analogue was not checked.
- Houghton H_n (n ≥ 3, Brown) is finitely presented although Z^{n-1} acts on the rays with infinitely many 2-orbits. The extension there is by eventual translations, not by a subgroup of Sym(X) acting regularly.
- The eventual-translation mechanism needs at least 3 coarse ends. For a one-ended X, "eventually a translation" collapses back to FSym(X)·G.

**Verdict: UNCLEAR.** It is probably circular for one-ended inputs, pending the Alt_fin analogue of Cornulier's criterion.

**Next test.** Decide whether Alt_fin(X) ⋊ G finitely presented ⇒ finitely many G-orbits on X².

## Approach 4. Dense finitely presented subgroups of homogeneous-structure automorphism groups (Fraïssé lens)

**Idea.**
- Type (A) needs only an fp Γ ≤ Aut(M) with finitely generated point stabilizers and finitely many orbits on 2-subsets, not full oligomorphicity.
- Model case, hand check: Thompson F acting on the dyadic rationals in (0,1).
  - It is faithful and highly order-transitive, with one orbit on 2-subsets.
  - The stabilizer of a dyadic point is F × F.
  - So it is type (A), inside Aut(Q,<).
- Plan: for each decidable G, build a homogeneous structure M_G whose finite configurations carry G-labels, e.g. the Fraïssé limit of finite partial G-labelled configurations. Aut(M_G) then contains G. Look for a finitely presented dense subgroup generated by Thompson-like local moves.
- The complexity principle then just says stabilizer membership must encode G's word problem, which the labels do.

**Would prove.** PBH for every input whose labelled structure has such a Thompson-like fp dense actor.

**Kill tests run.**
- **arXiv:2506.02319.** No conflict: it obstructs FP∞ of finite-set stabilizers for linear or finite-vcd groups. It says nothing about finitely generated point stabilizers, and these actors need not be linear.
- **Known finitely presented actors of this kind.** They exist for (Q,<) (F) and for Cantor space (V). I found none in the repo for the random graph or the Urysohn space. This was not searched exhaustively.

**Verdict: UNCLEAR.**

**Next test.** Does any finitely presented group act on the vertices of the random graph with finitely generated stabilizers and finitely many orbits on 2-subsets?

## Approach 5. Groupoid or inverse-semigroup inputs to the SV construction

**Idea.** Replace the actor group G by an étale groupoid of partial bijections of S, e.g. local moves of G's Cayley graph. The input then need not be a finitely presented *group*.

**Kill test (repo node, done).**
- The resulting groups are full Cantor groups containing standard V.
- `fp-full-binary-cantor-groups-have-type-a-actions` already turns any finitely presented such group into a type (A) actor.
- So finite presentation of the groupoid version is exactly the open full-Cantor-envelope clause of the shell routes.

**Verdict: KILLED as a duplicate** of the existing full Cantor envelope route. It gives no new mechanism, and it is not a disproof.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Commensurated / Schlichting actors | killed (finite bi-index + commensurated ⇒ finite index) |
| 2 | One actor with a universal permutation normalizer | survives as a reformulation, no candidate |
| 3 | Finitary-by-input Alt_fin(X) ⋊ G | unclear, probably circular for one-ended inputs |
| 4 | Dense fp subgroups of Aut(M_G) | unclear |
| 5 | Groupoid inputs to SV | killed as a duplicate of the full Cantor envelope route |
