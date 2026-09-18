---
rg: 2
id: boone-higman-conjecture
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented simple group
root: true
goal: true
distinct_from:
  boone-final-group-finitely-presented: that is one established fact about one constructed group -- the Boone tower's final group has a finite presentation; this is a universal embedding conjecture over all finitely generated groups with solvable word problem, and it requires the target to be SIMPLE, which that tower's final group is not.
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's classical theorem, which is true and imposes no finiteness on the presentation of the envelope; this asks for the envelope to be finitely PRESENTED, which is exactly the part Schupp does not give and which fifty years of work have not supplied.
  simple-sofic-total-mf-radical: that asks for a countable simple sofic group whose MF radical is everything -- an approximation property of one constructed group; this is a universal embedding statement with no approximation content, and neither implies anything about the other.
  literal-word-problem-solvable: that computes the word problem of one specific group E built in this repository; this quantifies over all finitely generated groups with solvable word problem and asserts an envelope exists for each.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group whose word problem is undecidable, which is the other side of the same dividing line; this is about the groups on the decidable side and where they can be embedded.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-gpu-pilot-2026-09-08.md
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
  - research/artifacts/boone-higman-steinberg-cover-correction-2026-09-08.md
  - research/artifacts/boone-higman-cover-kernel-dichotomy-2026-09-08.md
  - research/artifacts/boone-higman-lean-preflight-2026-09-08.md
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
  - research/artifacts/boone-higman-zigzag-shift-compiler-2026-09-08.md
  - research/artifacts/boone-higman-finite-ray-compiler-boundary-2026-09-08.md
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md
  - research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
  - research/artifacts/boone-higman-perfect-shell-route-2026-09-08.md
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-arithmetic-odometer-model-2026-09-08.md
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

For every finitely generated group `G` with solvable word problem there is a
finitely presented simple group `H` and an embedding `G <= H`.

Open since the 1970s.  Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356,
state the two-directional form: "A conjecture of Boone and Higman from the
1970's asserts that a finitely generated group `G` has solvable word problem
if and only if `G` can be embedded into a finitely presented simple group."

Only the direction above is open.  The converse is a theorem and is carried
separately as `simple-envelope-forces-solvable-word-problem`.

## Why it is a root of this graph

It is an explicit program goal, and remains open. Its existing embedding
routes originated when an external resolution attempt was audited against
this repository on 2026-08-17 and turned out to land squarely on machinery this repository
already owns: the missing hypothesis of its near-solution is finite normal
generation of a maximal kernel, which by
`fp-quotient-iff-kernel-finitely-normally-generated` is
*equivalent* to finite presentation of the resulting simple quotient — and
the hard half of that equivalence is already formalized here, in
`GroupApproximation/Algebra/FinitePresentationKernel.lean`.  The attempt also
runs its ring lane straight through this repository's Leavitt formalization,
where one tempting route is killed outright and another is left needing a
theorem nobody has.

Soficity, hyperlinearity and MF-ness are not evidence about this claim in
either direction, and no node here pretends otherwise.

The September 8 construction
`boundary-orbit-cyclic-wreath-has-fp-simple-envelope` handles cyclic
lamps on constant-ray orbits of contracting self-similar groups. Its
proof uses `contracting-srn-rational-stabilizers-are-fp` and a finite
germ extension. It supplies an additional positive family, not a
universal route: no reduction from arbitrary solvable-word-problem
inputs to that construction has been established. The attached
artifact explains the residual-finiteness limit on its input family.

There is a stronger limit on finite-state realizations:
`decidable-fp-groups-need-not-embed-in-rational-group` combines an
explicit single-exponential transducer word-problem algorithm with
the Kharlampovich--Myasnikov--Sapir hardness theorem. Some decidable
finitely presented residually finite inputs embed in no rational
homeomorphism group. Thus a universal proof cannot require every
input to act by finite-state Cantor homeomorphisms.

The route `boone-higman-via-shell-germ-stabilizers` retains arbitrary
Cantor shell homeomorphisms and therefore avoids that restriction.
Its universal faithful finite-germ realization is proved; its OPEN
clause is `decidable-inputs-have-fp-shell-stabilizers`, finite
presentation of three explicitly specified one- and two-point
singularity stabilizers for a suitable enumeration of the input.

`virtually-cyclic-inputs-have-fp-shell-stabilizers` closes these clauses
for virtually cyclic inputs. The normal-core criterion used there is
unavailable for every other input, as the prefix-core classification
proves. For arbitrary inputs the germ group instead has the exact
index-two fiber-product description in
`shell-germ-group-has-index-two-fiber-product`. Finite presentation
of that fiber product is necessary for the open shell clauses; neither
the universal presentation nor a lift back to all three stabilizers
has been supplied.

## What a certificate must contain

The shell route has an additional effective consequence:
`shell-recursive-presentations-compute-enumerations` extracts the
regular enumeration from a recursive presentation of its one-point
stabilizer. A successful enumeration must therefore be computable.
The finite-prefix obstruction for shell groups shows why finite point
samples do not certify a successful presentation, even for Z.

The shorter route `boone-higman-via-fp-shell-envelopes` now asks only
for a finitely presented E_nu. Finite generation of its point stabilizers
holds for every enumeration of every finitely generated input, by
`shell-finite-point-stabilizers-are-finitely-generated`. The three
stronger stabilizer presentation clauses remain sufficient, but the
new route does not assume them or finite presentation of the germ group.

There is also the direct route `boone-higman-via-perfect-shell-envelopes`.
An explicit HNN and amalgam construction embeds every finitely
presented decidable input in an infinite perfect one while preserving
decidable word problem. Its shell envelope is simple for every
enumeration. The remaining OPEN task is finite presentation of that
envelope for a suitable enumeration; this route needs no additional
twisted Brin--Thompson construction.

*Proof.*  It suffices to close any one of the live routes.  The shortest
is `boone-higman-via-ck-maximal-kernel`: by
`boone-higman-thompson-simple-envelope` and
`chatterji-kassabov-normal-generator-embedding` one already has, for every
such `G`, a chain

    G  <=  S  <=  Gamma

with `S` finitely generated, computably presented and simple, and `Gamma`
finitely presented with property (T) and normally generated by an element of
`S`.  By `proper-normal-subgroups-miss-the-normally-generating-core` every
proper normal subgroup of `Gamma` meets `S` trivially, so every maximal
proper normal quotient is simple and still contains `G`.  A certificate is
then exactly a finite normal generating set for one maximal proper normal
subgroup of `Gamma`.

Two routes added 2026-08-24 avoid the normal-lattice machinery entirely and
never require any group to be shown simple, because simplicity is produced at
the end by `type-a-action-gives-boone-higman-for-subgroups`.  A certificate
for either is a construction and nothing else:
`universal-fiber-product-data-for-word-problem-groups` asks for a finitely
presented overgroup with a finitely generated normal subgroup having trivial
centralizer, finitely many conjugacy classes and an `F_3` quotient;
`shift-higman-compiler` asks for finite presentability of one explicit
permutation group built from a chosen enumeration.  Both are shown to force
their input to have solvable word problem
(`compilers-cannot-drop-the-decidability-hypothesis`), so neither can be
proved by an argument uniform in a finite presentation.  See
`research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md`.

*Disproof.*  A finitely generated group with solvable word problem together
with a proof that it embeds in no finitely presented simple group.  No
mechanism for the second half is known; see the diagonalization entry below.

## Attempts

Seven lanes were run against this repository's material on 2026-08-17.
The universal-sandwich ring lemma is valid, but its claimed consequence
that the elementary group is finitely presented was withdrawn on September
8: the cited theorem applies to the Steinberg group. The corrected
construction retains a marked cover. Several shortcuts are recorded as
dead routes with named invalidators; the rest remain at identified gaps.
The August audit and the September correction artifacts carry the arguments.

1. **Take a maximal normal quotient of the finitely presented envelope.**
   *Dies* at `fp-quotient-iff-kernel-finitely-normally-generated`:
   a quotient of a finitely presented group need not be finitely presented,
   and Zorn's lemma supplies a maximal kernel and nothing else.  Recorded as
   `boone-higman-via-maximal-quotient-of-the-envelope`.
2. **Zorn on the finitely normally generated proper normal subgroups.**
   *Dies* on chains: the union of an ascending chain of finitely normally
   generated normal subgroups need not be finitely normally generated, so the
   class has no upper bounds and Zorn does not apply.  Finite generation of
   the ambient group gives properness of the union, not stabilization of the
   chain.  What would rescue it is a Max-n condition on the normal lattice,
   and none was found.  Deferred rather than noded: nothing is refuted.
3. **Property (T) as a source of that Max-n condition.**  *Dies as a general
   principle.*  By
   `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`, one torsion-free
   finitely presented word-hyperbolic property-`(T)` group has continuum many
   maximal normal subgroups that are not finitely normally generated.  Hence
   even those combined hypotheses do not imply normal-lattice Noetherianity.
   The construction-specific possibility that the Chatterji--Kassabov
   elementary-matrix envelope has one specially chosen compact maximal kernel
   remains open.
4. **Make the coefficient ring simple.**  Split in two.  The naive form —
   the one-relation universal sandwich already gives a simple ring — *dies*
   at `one-sided-sandwich-leaves-an-ideal-missing-the-core`, by an explicit
   Toeplitz counterexample; recorded as
   `boone-higman-via-sandwich-ring-simplicity`.  The serious form survives as
   the open route `boone-higman-via-projective-ring-host`. Its predecessor
   `boone-higman-via-finitely-presented-simple-ring-quotient` is invalidated:
   its universal ring premise fails in composite characteristic, and its
   unquotiented elementary group has a nontrivial central involution.
5. **Use this repository's finitely presented strongly simple Leavitt algebra
   as a universal host.**  *Dies* in every characteristic.
   - In characteristic zero at `weyl-algebra-blocks-a-universal-leavitt-host`:
     Bilich--Hazrat--Nam prove the first Weyl algebra does not embed in
     `L_K(1,2)` when `char K = 0`.
   - Over `F_2`, where the Weyl argument fails, at
     `fixed-leavitt-hosts-cannot-be-universal-bh-containers`: a fixed decidable
     host has one word-problem time bound.
   Recorded as `boone-higman-via-universal-leavitt-host`.
6. **Compress the infinite Boone--Higman HNN tower into finitely many
   relators**, by a shift `t_i = z^{-i} t z^i` encoding the enumeration.
   *Deferred at an identified step.*  Encoding the recursive list is
   Higman's theorem and is not the difficulty; the difficulty is that every
   nontrivial element of the *final* group must normally generate it,
   including the new machine and stable letters, and forcing that with extra
   relations endangers the base embedding.  Finite compression that preserves
   simplicity is the conjecture restated, so nothing is invalidated.
7. **Diagonalize for a counterexample.**  *Deferred, no mechanism.*
   Cardinality separates nothing — both the finitely presented simple groups
   and the computably presented finitely generated groups are countable.
   Higman's embedding theorem forbids diagonalizing against all finitely
   presented targets, so simplicity must be used essentially, and finite
   presentations defining *simple* groups are not available as an effective
   list with the semantic guarantees a priority construction needs.  No
   hereditary separating property was found beyond solvable word problem,
   which the candidate has by hypothesis.  Non-uniformity is not a disproof
   either: the conjecture is existential, so incomputability of
   `presentation |-> simple envelope` is consistent with it.

8. **Tits' independence property as the simplicity engine** (heretic lane,
   2026-09-17).
   - *The idea.* The families here share three unstated assumptions:
     - simplicity comes from a Cantor full group, ring units or a maximal kernel;
     - finite presentation is certified on one overgroup through pair-orbit
       finiteness;
     - hardness must be carried by the actor's own stabilizers.

     Denying all three at once gives the following scheme. Take an amalgam
     `A *_C B` of finitely presented groups over a finitely generated `C`. It is
     finitely presented for free. Tits' property (P) on its Bass--Serre tree gives
     simplicity when `C` normally generates `A` and `B`, and the word problem is
     only as hard as membership of `C` in `A` and `B`.
   - *Where the geometric version dies.* By
     `tits-independence-amalgams-force-self-product-edge-groups`, a faithful
     amalgam with (P) and `C ≠ 1` has `C = V × W` with `V ↪ V × V`. So `C`
     contains `Z^k` or `(Z/p)^k` for every `k`. Therefore `C` cannot be finite,
     hyperbolic, proper cocompact CAT(0), or of finite virtual cohomological
     dimension, and neither can any overgroup of `C`. That kills small-cancellation
     and Rips-type vertex groups, where hard membership problems are cheap.
   - *Every independence engine, not only amalgams.* Take a faithful, minimal
     general-type tree action with Tits' (P), or with Banks--Elder--Willis
     `(P_k)`, and some nontrivial edge fixator. By
     `micro-supported-tree-actions-self-embed-rigid-stabilizers`, every
     half-tree rigid stabilizer `R` contains `⊕_N R`. So the same bounded-rank
     classes are excluded for `Γ`, `Γ⁺` and `Γ^{+k}`.
   - *Where the locally finite version reduces.* Take a locally finite tree with
     (P). By `tits-independence-vertex-groups-are-branch-type`, each
     ball fixator is the direct product of the level rigid stabilizers. So vertex
     stabilizers are residually finite branch-type groups, and they are branch
     groups when the local actions are 2-transitive. If `Γ` and its edge
     stabilizers are finitely presented, the vertex stabilizers are finitely
     presented too. The locally finite Tits route therefore needs a finitely
     presented branch-type group. No finitely presented branch group is known
     (Bartholdi--Grigorchuk--Šunić). The route also cannot contain an infinite
     simple Kazhdan input.
   - *What is left.* Edge groups with self-similar direct products, as in Thompson
     groups or branch groups. It is open whether any finitely presented group acts
     faithfully on a tree with (P), a nontrivial finitely generated edge group, and
     not both indices 2.
   - *The finitary infinite-valence route dies* (heretic lane w3-030,
     2026-09-17). By `finitely-singular-tree-hosts-have-no-fg-stabilizers`, fix
     a core `G ≤ Aut(T)` in which only `1` fixes an edge, and a radius `ρ`. Any
     group of automorphisms that agree with elements of `G` on `ρ`-balls off
     finitely many singular vertices, and that acts minimally without fixed end
     with some nontrivial rigid stabilizer, has no finitely generated vertex,
     edge or rigid stabilizer. This holds in every valence.
     - *Where it fails.* The singular depth `D` is ultrametric on each
       stabilizer, so a finitely generated stabilizer subgroup has bounded
       depth. But every nontrivial deep rigid element has a deep singularity.
     - *What it kills.* Le Boudec-type local-rule groups, their countable-colour
       analogues, and the finitary (P)-closures of free products. None of these
       can host (P) with a nontrivial finitely generated edge group.
     - *What is left.* A host with that property needs elements that are
       infinitely singular over every such core, of automaton or branch type,
       as in `tits-independence-vertex-groups-are-branch-type`.
   - *The section-closed locally finite route dies* (prover lane w6-030,
     2026-09-18). `fully-self-replicating-tree-groups-give-fg-tits-hosts` builds a
     finitely generated simple host `(R ≀ A_{d+1}) *_{R×R} (R ≀ A_{d+1})` from a fully
     self-replicating `R ≅ R ≀_X A_d`. It is finitely presented iff `R` is. By
     `self-wreathing-groups-are-not-fp-infinity`, every iterated wreath product of `P`
     is a retract of any `R ≅ R ≀_X P`. So `H_k(R)` contains `H_k(P)^n` for every `n`,
     where `k` is the first nonzero degree of `P`.
     - *Where it fails.* For `d = 3, 4`, `k = 1`, and `R` is not finitely generated.
       For `d ≥ 5`, `k = 2` (Schur multiplier `Z/2`), and `R` is not finitely presented.
       This holds with or without contraction. No `R ≅ R ≀ P` with `P ≠ 1` finite is
       `FP_∞`.
     - *What is left.* Hosts whose point-stabilizer local action is superperfect, such
       as `M_12 ⊃ M_11` or `M_24 ⊃ M_23`, where the argument only rules out `FP_3`.
       Also left are non-split self-branching groups, where `R^X ⊴ R` has no complement.
   - *The superperfect escape is open at FP_2, and the non-split escape is empty*
     (prover lane w7-030, 2026-09-18). See `tits-hosts-for-transitive-local-actions`.
     - *What holds.* The Krasner--Kaloujnine cocycle `κ(σ,c) = τ_{σc}^{-1} σ τ_c`
       replaces the `A_{d+1}` parity lemma. So the host
       `(R ≀_C F) *_{R×R} (R ≀_C F)` exists, and is simple with (P), for every transitive
       `F` generated by its point stabilizers. It is finitely presented iff `R` is.
       A finitely presented host of this form therefore needs a superperfect `F_0`.
       For `F = M_12`, the group `R = ⟨M_11, b⟩` with `b = (b, α, β, 1, …)` is fully
       self-replicating, checked in GAP. It gives a finitely generated simple (P) group
       on `T_12`. It is bounded, hence contracting, and Bartholdi's theorem kills it.
     - *Where it fails.* For superperfect `F_0`, every congruence quotient and every
       retract `W_n` is superperfect. So no finite-quotient or retract argument can
       reach `FP_2`.
     - *Non-split.* The non-split case cannot occur in a section-closed host, because the
       rooted `F_0` is always a complement there. Without a complement, the transfer
       through `Stab_R(n)` dies: the index `|W_n|` grows exponentially, while the
       available homology `H_k(W_n)` grows only linearly in `n`.
     - *What is left.* A non-contracting finitely presented fully self-replicating `R`
       with root image `M_11`, `M_23` or `PSL(2,8)`. This is a case of the open
       finitely presented branch-group question.
   - *What is left.* A Tits-(P) host needs infinite valence, or edge stabilizers
     that are not finitely presented, or a positive answer to the finitely
     presented branch-group question. The open first step is whether some
     finitely presented group acts faithfully and minimally, with no fixed end,
     on a tree of infinite valence with (P) and a nontrivial finitely generated
     edge group. There the ball fixator only contains the restricted product of
     rigid stabilizers, and the branch-type conclusion lapses.
9. **A universal host from rewriting-system dynamics** (reframer lane sw-010,
   2026-09-17).
   - *The idea.* Feed a hard finitely presented group into
     `fp-self-similar-groups-embed-in-fp-simple-groups`. To do that, make it
     self-similar by letting its tree action be read off a canonical
     endomorphism: a generator substitution respecting the relations, or a
     Frobenius-type scaling of the Kharlampovich--Myasnikov--Sapir groups.
   - *Where it dies.* By `virtually-endomorphic-self-similar-actions-have-finite-image`,
     suppose the sections agree, on a finite-index subgroup, with endomorphisms of
     a finite-index normal subgroup `G'`. Then the fully invariant subgroup
     `R_n(G')` is carried into itself by every section, so it acts trivially.
     The action therefore has finite image.
   - *What is left.* Only "division" sections escape: section maps that extend
     to no endomorphism, like the adding machine or Cartier-type digit
     contractions. Whether a Cartier-type virtual endomorphism of a
     Kharlampovich--Myasnikov--Sapir group gives an infinite-state faithful
     action is open.

9. **Just-infinite lattice hosts via the Bader--Shalom normal subgroup theorem**
   (heretic lane c-bhdec1, 2026-09-17).
   - *The idea.* The families here share three further unstated assumptions:
     - finite presentation must be engineered on the host;
     - simplicity is proved element by element in a group with no finite
       quotients;
     - the host is a discrete transformation group built from the input's
       combinatorics.

     Deny them in turn. Finite presentation passes for free to finite-index
     subgroups and retracts. Simplicity can come from global just-infiniteness
     plus one simple subgroup. The host can be a uniform lattice in a product of
     locally compact groups.
   - *Established.* `just-infinite-over-simple-subgroup-gives-fp-simple-host`: a
     finitely generated group that is just-infinite above an infinite simple
     subgroup `S` is virtually `T^k` with `S ↪ T` simple, and `T` is fp iff the
     host is. Hence `boone-higman-iff-fp-just-infinite-hosts`: the conjecture is
     equivalent to embedding every infinite decidable finitely generated group in
     a finitely presented just-infinite group. Also imported:
     `bader-shalom-normal-subgroup-theorem` and
     `product-lattice-fp-iff-factors-compactly-presented`.
   - *The route.* `boone-higman-via-bader-shalom-lattice-hosts` has two independent
     OPEN prerequisites:
     - `decidable-simple-groups-embed-in-bader-shalom-lattices` (P1);
     - `simple-in-bader-shalom-lattice-forces-compact-presentation` (P2).

     P2, the cheaper one, was attacked. It reduces exactly to finite presentability
     of the simple group `T` read off the lattice.
   - *Where it dies.* P1 dies for three classes of factors:
     - linear factors, on either side: the projection is injective, so the host is
       residually finite;
     - two Haagerup factors: the simple Kazhdan probe from
       `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` is squeezed into a
       compact set;
     - properly cocompact CAT(0) factors: complexity bound, conditional on the
       unpinned BORS bound of Idea 14 in
       `research/artifacts/ideas-bh-round2-2026-09-14.md`.

     This covers every Burger--Mozes-type and arithmetic example. P1 needs a
     genuinely new lattice in a product of two non-linear, non-Haagerup, non-CAT(0)
     factors.

A ninth non-attempt, recorded because it looks tempting from inside this
program: Schupp's envelope
(`countable-group-embeds-in-two-generator-simple-group`) is two-generator but
not computably presented, so Higman's theorem does not apply to it;
`boone-higman-thompson-simple-envelope` restores computable presentability
but then Higman destroys simplicity.  That route rotates between the
conjecture's two halves without narrowing either.

10. **The hereditary separating property of Attempt 7, named** (heretic lane
    swarm-0917-w4-bh-heretic, 2026-09-17).
    - *Result.* `boone-higman-iff-isolated-hosts-and-local-boone-higman`
      (ESTABLISHED): the conjecture holds iff both
      `every-decidable-group-embeds-in-an-isolated-group` and
      `local-boone-higman-conjecture` hold.
    - *The lemma.* `isolated-embedding-is-one-existential-sentence`: an
      isolated `H` embeds in `S` iff `S` satisfies one existential sentence
      `Σ_H`, built from a finite presentation and a finite discriminating set.
    - *Consequence.* A counterexample is either a decidable group with no
      isolated overgroup, or a finite system `(E, N)` with a decidable model and
      no model in any finitely presented simple group.
    - *Kills.* The other invariant classes in the counterexample brief die as
      forced properties at named steps (`local-boone-higman-conjecture`,
      Attempt 2):
      - torsion-problem undecidability, because `2V` has undecidable torsion
        problem;
      - Dehn functions, killed on main;
      - input finiteness type, because finite groups and `Z ≀ Z` lie in `V`.
    - *Route.* `boone-higman-via-isolated-overgroup-and-local-boone-higman`.

11. **Approximation properties as the separating property of Attempt 7**
    (transplanter lane swarm-0917-w5-pull-z-5, 2026-09-17).
    - *Result.* `hereditary-approximation-disproofs-of-boone-higman`
      (ESTABLISHED). A hereditary class `P` disproves the conjecture iff every
      finitely presented simple group is in `P` and some decidable group is not.
    - *Kill.* Every `P` contained in soficity or in MF-ness dies at the first
      step. The witness is a finitely presented simple nonsofic group, or one
      with full MF radical.
    - *Survivors.* Any survivor contains the Leavitt unit group, so it contains
      a nonsofic group. For hyperlinearity, a disproof needs all of the
      following:
      - no infinite finitely presented simple group is HS stable;
      - `binary-leavitt-unit-group-hyperlinear`;
      - a nonhyperlinear decidable group.
    - A table-defined separator refutes `local-boone-higman-conjecture` with a
      single finite system.

12. **Exactness as the separating property of Attempt 7** (transplanter lane
    c-pz3, swarm-0917, 2026-09-18).
    - *Lemma.* `decidable-residually-finite-non-exact-group-exists`
      (ESTABLISHED, unreviewed). Osajda's recursive residually finite
      non-exact group has solvable word problem: a word of length `≤ n` is
      trivial in `G` iff it is trivial in the finitely presented residually
      finite stage `G_n` (his conditions (C) and (D)), and McKinsey decides
      `G_n` uniformly. With `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`
      this gives a non-exact decidable simple Kazhdan LEF group.
    - *Result.* `exactness-separates-boone-higman-iff-fp-simple-groups-exact`
      (ESTABLISHED, unreviewed). (S2) holds for exactness, so exactness
      disproves the conjecture iff every finitely presented simple group is
      exact. If the conjecture holds, `fp-simple-nonexact-group` (OPEN) holds.
    - *Kill.* Invariant: property A. Step: the universal embedding step.
      Every class of exact hosts dies there, even for residually finite
      inputs: linear groups, hyperbolic groups, cocompactly cubulated groups,
      lattices on products of trees, finite asymptotic dimension. Unlike
      Attempt 11, the decidable side is unconditional, since the witness is
      sofic and hyperlinear.
    - *Survivors.* A host class carrying the conjecture must contain
      non-exact groups. The exactness of `V`, `nV`, `SV_G` and `L^x` is not
      settled in this graph.
13. **Følner growth of amenable subgroups as the separating property of
    Attempt 7** (transplanter lane w7-z, swarm-0917, 2026-09-18).
    - *Separators.* `P_U` is the class of groups whose finitely generated
      amenable subgroups `H` all have `F_H ≼ U`.
      `folner-separators-of-boone-higman` (ESTABLISHED, unreviewed) shows that
      `P_U` is hereditary, and that for recursive `U` it separates iff every
      finitely presented simple group lies in `P_U`.
    - *Lemma (decidable side).*
      `decidable-amenable-groups-have-no-recursive-folner-bound` (ESTABLISHED,
      unreviewed). For every recursive `U`, a Brieussel--Zheng diagonal product
      with expander factors chosen against `U` is decidable, elementary
      amenable, and has `F ⋠ U`.
    - *Kill 1.* Invariant: tower height. Step: (S1). Every `U ≼ exp_k` fails,
      because `Z wr (... wr Z)` with `k+2` factors lies in `B_A` and has
      `F ⋠ exp_k` (`iterated-wreath-products-of-z-have-tower-folner-functions`,
      from Erschler's wreath formula).
    - *Kill 2.* Invariant: membership in one c.e. class of amenable
      presentations. Step: the choice of witness. Any proof that no recursive
      `U` works, with witnesses taken from a uniformly computable family of
      amenable subgroups of finite presentations, dies at Cavaleri's uniform
      bound `U_*`. So a proof must use the totality of `U`.
    - *Result.* The conjecture implies
      `fp-simple-amenable-subgroups-beat-every-recursive-folner-bound` (OPEN),
      by `fp-simple-amenable-folner-growth-via-boone-higman`. A single
      recursive `U` above every tower with (S1_U) would disprove the
      conjecture. The live unconditional step is to embed the diagonal
      products in finitely presented simple groups. They are
      locally-finite-by-`Z` and residually finite, but their envelope is an
      unrestricted wreath product, so the `B_A` wreath closure does not
      reach them.

**September 17: one decidable host per complexity bound.**  This attempt
decomposes the conjecture as follows.

- *(i)* For every recursive `T`, one decidable `U_T` contains every input
  with word problem in `F(T)`.
- *(ii)* Each `U_T` embeds in a finitely presented simple group.

It is recorded as `boone-higman-via-complexity-graded-universal-inputs`.

*Dies* at (i), for `T(n) = 2^((n+1)^37)`.  The Birget--Ol'shanskii--Rips--Sapir
embedding is computable from the acceptor
(`bors-embedding-is-effective-in-the-machine`).  Feeding it the free-or-abelian
acceptors indexed by halting gives a computable family of finite presentations
`H_e`.  Each has Dehn function `≼ n^18`, and `[x_e, y_e] = 1` in `H_e` iff
`phi_e(0)` halts (`polynomial-dehn-fp-groups-have-nonuniform-word-problem`).

A decidable host of all `H_e` would decide halting by a homomorphism search
(`no-decidable-group-contains-every-polynomial-dehn-fp-group`).  The same
uniform Kuznetsov search rules out computing a finitely presented simple
overgroup from a presentation with polynomial Dehn function, or from an NP
acceptor with unknown constant
(`fp-simple-envelopes-not-computable-from-presentations`).
A constructive proof must consume a total decision procedure of the input, not
a presentation or a complexity grade.

## A strictly easier subproblem, unsolved

If a maximal proper normal `M <| Gamma` could be chosen *recursively
enumerable as a normal subgroup* relative to a finite presentation of
`Gamma`, then `Gamma/M` would be a finitely generated computably presented
simple group with decidable word problem — not finitely presented, but an
effective simple envelope produced directly from the construction.  The
obvious effective-Zorn attack needs to decide `<<M, x>> ∩ S = 1`, and the
clean criterion of `proper-normal-subgroups-miss-the-normally-generating-core`
(`N` proper iff `N ∩ S = 1`) is not effective in the required direction.

## August 2026 property-(T)-free normalization

`bht-trivial-normal-intersection-envelope`, imported from
Fournier-Facio--Wu--Zaremsky Appendix A, shows that the near-solution does not
intrinsically need the Chatterji--Kassabov property-`(T)` envelope.  Every
finitely generated solvable-word-problem group embeds in a finitely presented
`P` while missing **every** proper normal subgroup of `P`; equivalently every
nontrivial quotient of `P` preserves the input.  Thus the simple-core survival
part is a theorem in a property-`(T)`-free form.  The remaining obstruction is
unchanged and exact: a maximal kernel supplied by Zorn need not be finitely
normally generated, so its simple quotient need not be finitely presented.

## September 8: the canonical coset repair fails for every quotient

`ck-quotient-corner-has-infinite-bi-index` strengthens the direct-corner
obstruction: every nontrivial quotient retains a root subgroup isomorphic
to the additive group of the infinite quotient ring at its elementary
level, and that subgroup supplies distinct simple-core double cosets.
Marked covers inherit infinite bi-index by the surjection of double-coset
sets. Finite-index enlargements of the stabilizer cannot repair it either.

This refutes `ck-quotient-coset-repair` and disables
`boone-higman-via-ck-quotient-cosets`. Other embeddings and infinite
stabilizer enlargements remain candidates. The maximal-simple-quotient
route does not require finite bi-index and remains open.

The GPU pilot is an operational experiment attached to this goal, not a
mathematical prerequisite or a proof of any route. Its artifact records the
$20 spending cap, the provider's GPU-quota rejection, and the prepared neural
proposal/checker pipeline. Positive Lean calibration subsequently passed
on a cached remote CPU runner; the separate preflight artifact records
the exact scope and connects its normalization lemma to the quotient proof.
The dedicated research workflow checks source syntax, the exact `S3`
counterexample used as a negative control, and Cairn's graph structure.

## September 8: the ring route needs a projective target

`ring-simple-envelope-characteristic-obstruction` refutes the unrestricted
finite-fullness premise using `Z/6Z` and characterizes which coefficient
rings admit abstract simple unital envelopes. Integral group rings pass
that test, but the construction supplies no finite presentation.

`rank-four-elementary-center-obstructs-simplicity` shows that `EL_4(L)`
cannot be the proposed simple group whenever `L` contains `Z`: it contains
the proper central subgroup `{I_4,-I_4}`. The repaired conditional route
`boone-higman-via-projective-ring-host` proves the simple core survives
projectivization. Its missing hypothesis explicitly asks for a finitely
presented, simple projective target. That existence problem remains open.

## September 8: finite presentation belongs to the Steinberg cover

`steinberg-finite-presentation-and-kazhdan-theorem` pins the imported
finite-presentation result to `St_4(U)`. It does not make `EL_4(U)`
finitely presented. `finite-marking-normal-generator-cover` proves that
finitely many added relators preserve a finitely presented marking and
force the prescribed normal generator while retaining a map to the matrix
group. Applied to the Steinberg source, this gives
`ck-steinberg-marked-cover`.

The maximal-kernel route remains valid for this finitely presented cover.
The matrix level-ideal screen cannot automatically be applied to its
arbitrary maximal kernels. The quotient-and-cover double-coset obstruction
still applies in its stated scope, independently of finite presentation
of the matrix group. No finite normal generating set for a maximal kernel
has been supplied.

## September 8: a coset repair must come from the covering kernel

`ck-cover-quotient-kernel-dichotomy` settles the scope of quotients that
escape the matrix map. Write `K=ker(Gamma->EL_4(U))`. Any proper quotient
`Gamma/M` in which the inherited core has finite bi-index must satisfy
`Gamma=MK`; equivalently K surjects onto the whole quotient. For maximal
M this is the alternative to containing K and descending to a simple
matrix quotient. No suitable quotient of K has been constructed, and no
finite normal generating set for M follows from this dichotomy.

## September 8: projectivization retains the presentation requirement

`projective-elementary-fp-kernel-criterion` gives an exact version of the
ring host's finite-presentation clause. It requires finite normal
generation of the unstable Steinberg kernel and finite generation of the
elementary center. A finitely generated group with finitely presented
central quotient is itself finitely presented, so passing to the
projective group does not repair failure of elementary-group finite
presentation. The ring-host route now uses the equivalent generating-data
formulation. Projective simplicity also forces the ring itself to be
simple. Neither the required generating data nor a universal host has
been constructed.

## September 8: an explicit positive cyclic shift compiler

`zigzag-cyclic-shift-envelope-is-finitely-presented` identifies a concrete
E_nu(Z) as an index-12 subgroup of E_4. Its finite presentation follows
from the four-ray Houghton group's finiteness theorem. The universal
infinite-input compiler remains open.

The same analysis shows a limit on testing enumerations by finite point
values: for Z every finite prescription extends to both a finitely
presented envelope and a non-finitely-presented one. The positive example
works because a global four-ray rule controls the relations. No analogous
global rule has been supplied for arbitrary decidable inputs.

The finite-ray generalization is now classified by
`finite-ray-shift-envelopes-require-virtually-cyclic-input`: it is possible
exactly for virtually cyclic inputs. In particular, Z^2 cannot be handled
by merely increasing the number of periodic rays. Its regular enumeration
also has unbounded generator displacement, as quantified by
`regular-enumeration-displacement-bounds-growth`. The shift route remains
open with these construction restrictions recorded explicitly.

## September 8: the universal computable-core automorphism upgrade fails

`relative-automorphism-fp-host-reflects-base-presentation` proves that a
finitely presented subgroup of Aut_G(G*F_n) containing the canonical
translation copy of a finitely generated G forces G itself to be finitely
presented. The proof lifts finitely many automorphisms, their inverses,
and their presentation relators using only finitely many base relators.

For MIF simple cores the evaluation action is faithful. Thus its action
image is finitely presented exactly when the core already is. The regular
cyclic twisted Brin--Thompson group supplies an infinite, decidable,
finitely generated simple MIF core which is not finitely presented.
This refutes `bffhz-action-image-is-finitely-presented` as universally
stated here and disables `boone-higman-via-bffhz-action-image`.

The published BFFHZ Question 3.2 assumes a finitely presented core and is
not answered by this counterexample. Selecting special non-MIF cores or
using other actions is not excluded. No proof or disproof of Boone--Higman
follows from this obstruction.

## September 8: a new wreath-product source needs a projection repair

The source audit in
`research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md`
examines arXiv:2609.01868v1. Its proposed finite-presentation proof appeals
to a coefficient-forgetting projection toward another Cantor full group.
`cantor-prefix-subgroup-detects-every-normal-kernel` rules out a map
which both kills a nonidentity localized coefficient and preserves the
prefix subgroup faithfully. The coefficient projection of an ordinary
wreath product does not supply such a full-group map.

If the intended projection is only on a localized coefficient subgroup,
it exists but cannot detect the exponents of the lamps it kills. The audit
separates these interpretations explicitly.

This is a proof-step obstruction, not a counterexample to Theorem D of
that source. Its finite-presentation conclusion has not been imported as
an established premise. A repair would need to derive cancellation of all
lamp coordinates from the finite relations directly. No such repair has
been supplied here.

## September 8: retain the shell stabilizer in a larger presented group

`shell-coset-induction-preserves-core-freeness` allows an abstract
finitely presented overgroup Gamma of E_nu: keeping H=(E_nu)_p
gives a faithful Gamma/H action with finitely generated point
stabilizers. The remaining type (A) condition is finite bi-index
of H in Gamma. The route `boone-higman-via-shell-stabilizer-overgroups`
therefore permits E_nu itself to remain non-finitely-presented.
Its universal host hypothesis remains OPEN.

Ordinary presentation embedding theorems do not settle that
hypothesis. `shell-finite-biindex-hosts-require-large-intersections`
forces the shell envelope to meet every conjugate infinitely;
proper almost malnormal hosts fail. Separately,
`cantor-prefix-markings-compute-clopen-action` reconstructs an
existing spatial overgroup action from a recursive presentation
and a marked standard V. This supplies an effective action test
once the action exists, not an existence theorem for such a host.

The positive terminated-digit embedding does not supply this
retained-stabilizer host either: `terminated-digit-host-has-infinite-shell-biindex`
constructs infinitely many double cosets in H_(h,r), distinguished
by the number of collapsed fibers met by the image of the fiber
over p. The obstruction persists in larger groups containing that
host, while its finitely presented simple embedding remains valid.

The next construction enlarges the stabilizer in that same digit
host. `terminated-digit-fiber-stabilizer-repairs-shell-action`
proves that the full setwise fiber stabilizer K is finitely
generated and core-free, with exactly h+3 double cosets. Its
intersection with the shell envelope is the original point
stabilizer S, and [K:S] is infinite. Thus the obstruction for S
is bypassed by an actual larger stabilizer in this restricted model.

The route `boone-higman-via-enlarged-shell-stabilizers` permits such
enlargements for arbitrary perfect decidable inputs. Its universal
permutation-extension hypothesis is still OPEN; the arithmetic
example does not make a rational host available for all inputs.

## September 12: Leavitt tensor hosts

`leavitt-tensor-hosts-acyclic-steinberg-and-fp` transfers Khanh's
acyclicity and Steinberg comparison from `L = L_(F_2)(1,2)` to
`B ⊗ L` for every simple `B` with `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.
- If `B` is finitely presented, the unit group is finitely presented.
- If `B` is central simple, the unit group is simple
  (`central-simple-leavitt-tensor-unit-groups-are-simple`).

Ara--Cortiñas show that `K_*(L ⊗ L)` vanishes. Two results follow.
- `leavitt-square-unit-group-is-fp-simple-and-acyclic`: a second
  finitely presented simple Leavitt unit group.
- `char-two-surface-linear-groups-satisfy-boone-higman`: the finitely
  generated linear groups over characteristic-two fields of
  transcendence degree at most two satisfy the conjecture.

The full characteristic-two linear class is the new root
`char-two-linear-groups-satisfy-boone-higman`, blocked at
`leavitt-tensor-powers-have-trivial-k-theory`.

The same host theorem gives the route
`boone-higman-via-central-simple-leavitt-tensor-host`. Its one open
premise is `decidable-group-algebras-have-fp-central-simple-hosts`:
each decidable group algebra must embed in a finitely presented
central simple algebra whose Leavitt tensor has trivial `K_1` and
`K_2`.

Unlike `boone-higman-via-projective-ring-host`, this route needs no
finite normal generation of a kernel. The Steinberg kernel over
`B ⊗ L` is trivial by Khanh's comparison criterion.
