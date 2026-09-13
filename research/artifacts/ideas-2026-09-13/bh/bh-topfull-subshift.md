# Ideas: Boone–Higman through topological full groups of subshifts and ample groupoids

Idea lane `bh-topfull-subshift`, 2026-09-13. Target: `boone-higman-conjecture`.
Lens: realize every decidable finitely generated group inside a finitely presented
simple derived (or alternating) subgroup of the topological full group of an effective
subshift or ample groupoid.

These are exploration notes. Nothing here proves or refutes the conjecture, and no
Cairn node is edited. Every kill test below was actually run, against repository
nodes or abstracts. The checked sources are listed at the end, and the depth of each
check is stated where it is used.

## Facts used

Repository nodes on origin/main, statuses as read today:
- `periodic-approximable-subshifts-host-no-fp-simple-group` (ESTABLISHED): full groups of
  infinite minimal Z-subshifts contain no finitely presented infinite simple group.
- `zd-derived-full-group-fp-forces-finite-type` (ESTABLISHED, unreviewed): if
  `D([[Z^d ~ X]])` is finitely presented for a free minimal X, then X is of finite type.
- `zd-derived-full-group-fp-forces-quantum-rigidity` (ESTABLISHED, reviewed): for d = 2,
  finite presentation also forces quantum rigidity in characteristic other than 3 and 5.
- `labbe-shift-derived-full-group-is-finitely-presented` and
  `penrose-derived-full-group-is-finitely-presented`: both OPEN. So no free minimal
  Z^2 shift of finite type is known to have a finitely presented derived full group.
- `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` (ESTABLISHED), Consequence 3.
  Let Lambda be amenable, acting continuously on a compact X with a full-support invariant
  measure. Then every Kazhdan subgroup of `[[Lambda ~ X]]` is residually finite.
- `deligne-lattice-embeds-in-no-rover-nekrashevych-group` (ESTABLISHED): Deligne's lattice
  is a finitely presented Kazhdan group, has solvable word problem, and is not residually
  finite.
- `decidable-fp-groups-need-not-embed-in-rational-group`: finite-state (rational) Cantor
  hosts are not universal.
- `fp-simple-groups-with-arbitrarily-complex-word-problem` (OPEN): a necessary consequence
  of Boone–Higman.
- `twisted-brin-thompson-finite-presentation-criterion`: `SV_G` is finitely presented iff
  G is finitely presented, the action has finitely many orbits of 2-subsets, and point
  stabilizers are finitely generated. A faithful action makes `SV_G` simple and containing G.
- `subshift-elementary-group-word-problem-degree`: `WP(EL_3(LC(X,F_q) ⋊ Z))` is
  Turing-equivalent to `L(X)` for an infinite minimal X.

## Approach 1. Amenable-orbit hosts: Z^d tilings and simulation shifts of finite type

**Idea.** Take the most expressive dynamics available on Z^d:
- Durand–Romashchenko lift effective minimal shifts to minimal shifts of finite type one
  dimension up;
- Penrose- and Labbé-type free minimal shifts of finite type;
- encode the input's word problem in the language, and hope the derived full group is a
  finitely presented universal envelope.

**What it would prove.** A universal finitely presented simple envelope living on Z^d
dynamics.

**Kill test.** Does some decidable input fail to embed in every full group of a free
minimal Z^d-subshift?

**Result.** Yes: Deligne's lattice.
- Z^d is amenable, so a minimal Z^d-subshift carries an invariant measure, and minimality
  gives it full support.
- By Consequence 3 of `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`, every
  Kazhdan subgroup of `[[Z^d ~ X]]` is residually finite.
- Deligne's lattice is Kazhdan, decidable and not residually finite.

**Verdict: KILLED as a universal host.** It stays useful as a source of positive
examples. The constraint it leaves:

> **(C1)** A universal full-group host must have non-amenable orbits (no invariant
> measure of full support).

## Approach 2. Self-simulable non-amenable hosts: Clapham, then Barbieri–Sablik–Salo, then Nekrashevych

**Idea.**
- Clapham: the input G embeds in a finitely presented Lambda with solvable word problem.
- Put Γ = (Lambda × F_2) × F_2. It is a direct product of non-amenable finitely generated
  groups, so it is self-simulable (Barbieri–Sablik–Salo). Γ has decidable word problem.
- So Γ admits a nonempty strongly aperiodic shift of finite type Y. Pass to a minimal
  subsystem X ⊆ Y; the action on X is free.
- The translation group Γ sits in `[[Γ ~ X]]`, so G does too. Orbits are non-amenable,
  so (C1) holds.
- Nekrashevych: A(𝒢_X) is simple, lies in every nontrivial normal subgroup of the full
  group, and is finitely generated because subshift actions are expansive.
- Place the input inside A by first making it perfect. The root already records an
  HNN-and-amalgam construction that preserves decidability. The inclusion of a perfect
  subgroup of the full group into A still has to be checked against
  arXiv:1511.08241 itself; only the abstract was read.

**What it would prove.** Boone–Higman, from one premise:

> **(P2)** For some self-simulable Γ with decidable word problem and some free minimal
> Γ-subshift X (necessarily of finite type, if the Z^d theorem generalizes), A(𝒢_X) is
> finitely presented.

**Kill tests run.**
1. **Positive instances of (P2).** None is known even for Γ = Z^2: the Labbé and Penrose
   finite-presentation nodes are OPEN, and Nekrashevych (arXiv:2509.05524, quoted in the
   Penrose node) remarks that full groups of shift-invariant groupoids "are rarely
   finitely presented". That is a remark, not a theorem.
2. **Necessary conditions.** On Z^d, finite presentation forces finite type, and for d = 2
   quantum rigidity. If this generalizes to Γ, X must be a *minimal* shift of finite type
   on Γ. The Barbieri–Sablik–Salo abstract supplies strongly aperiodic ones, not minimal
   ones. Durand–Romashchenko give minimal ones only on Z^d.
3. **Deligne check.** It passes: the input sits inside through the translation group, and
   (C1) holds.

**Verdict: UNCLEAR.** This is a genuine reduction of Boone–Higman to (P2). But (P2) is at
least as hard as the open Labbé/Penrose finite-presentation questions, with no positive
instance known in any dimension ≥ 2.

## Approach 3. The complexity filter says which finiteness input decidability must supply

**Idea.** Boone–Higman forces finitely presented simple groups beyond every recursive
time bound. A host class with a uniform word-problem complexity bound cannot be
universal:
- Finite-state hosts are already excluded (`decidable-fp-groups-need-not-embed-in-rational-group`).
- Expanding and one-sided shift-of-finite-type hosts carry fixed finite automata in their
  germs.

For subshift full groups the word problem tracks the language:
- the Grigorchuk–Medynets fact recorded in `higman-host-restriction-stops-at-separating-partial-models`
  (Z case);
- `subshift-elementary-group-word-problem-degree` (the EL_3 version).

Durand–Romashchenko show that minimal shifts of finite type already realize every effective
minimal shift as a projection of subdynamics, and that some quasiperiodic ones have only
non-computable configurations. Finite type therefore does not cap complexity.

**What it would prove.** A necessary-condition filter, not a construction:

> **(C2)** The local rule set stays finite (finite type gives the presentation's
> relators); the input's algorithm must live in the globally admissible language of the
> host shift.

**Kill test.** Is any lens host class complexity-capped yet claimed universal? Rational
hosts: yes, and they are excluded. Multidimensional minimal shifts of finite type: not
capped, according to the Durand–Romashchenko abstract.

**Verdict: SURVIVES as a filter.** Caveat: the word-problem-equals-language equivalence is
verified in the repository only for Z-subshift cases. The Γ version is unverified.

## Approach 4. Use the full group as a type (A) actor instead of as the envelope

**Idea.** Skip simplicity of the full group. Take a finitely presented full group F
containing the input, act on one orbit of its unit space, and feed the action to the
twisted Brin–Thompson criterion.
- High transitivity on orbits would make the 2-subset orbit count finite.
- The remaining condition is finite generation of point stabilizers.

**What it would prove.** Boone–Higman, through `SV_F`, whenever such an F exists.

**Kill test.** Which points have finitely generated stabilizers in the model full groups?
Golan–Sapir (arXiv:1605.05387, abstract): in Thompson's F, the stabilizer of a finite set
U ⊂ (0,1) is finitely generated iff U consists of rational numbers. So only eventually
periodic points give finitely generated stabilizers there.

**Result.** The strongly aperiodic hosts of Approach 2 have no periodic points at all, so
by analogy their orbit stabilizers are infinitely generated. This is an analogy with F
only, not a theorem about Γ-subshifts.

**Verdict: UNCLEAR, leaning killed for free subshift hosts.** The constraint it leaves:

> **(C3)** Finitely generated stabilizers want eventually periodic orbit points, i.e.
> expanding one-sided structure. This pulls against (C1) and (C2), which want free,
> aperiodic multidimensional structure.

## Approach 5. Mixed product groupoid: expanding factor × self-simulable finite-type factor

**Idea.** Take 𝒢 = 𝒢_O × 𝒢_(Γ ~ X), where 𝒢_O is a one-sided shift-of-finite-type
groupoid and Γ, X are as in Approach 2.
- The first coordinate supplies expanding structure (Nekrashevych arXiv:1312.5654:
  locally expanding self-coverings give finitely presented V_f) and eventually periodic
  points, for (C3).
- The second coordinate supplies non-amenable orbits containing the input (C1) and
  unbounded language complexity (C2).

Twisted Brin–Thompson groups are already full groups of products of Cantor coordinates
permuted by an actor. This is the variant where the "actor" is a Γ-subshift groupoid
rather than a permutation action.

**What it would prove.** Boone–Higman, if the product full group is finitely presented,
with the input in its simple alternating subgroup.

**Kill test runnable today.** Structural only.
- Finite presentation of a product groupoid's full group is not automatic from its
  factors, and nothing checked here gives it.
- The Γ-factor still needs (P2) or a substitute.
- Stabilizers of points that are periodic in the first coordinate but free in the second
  mix both behaviours, and their finite generation is unchecked.

**Verdict: UNCLEAR.** It is the one combination found that is consistent with (C1), (C2)
and (C3) at once, so it is recorded as the most interesting lead of this lens.

## Summary of constraints found

- **(C1)** Universal full-group hosts need non-amenable orbits. Kazhdan subgroups of
  amenable-orbit full groups are residually finite, and Deligne's lattice is not.
- **(C2)** The input's complexity must sit in the global language of a finite-type shift,
  not in finitely many automata.
- **(C3)** The actor route wants eventually periodic points for finitely generated
  stabilizers.
- A single free shift of finite type satisfies (C1) and (C2) but plausibly fails (C3).
  Product groupoids (Approach 5) are the natural way to reconcile them.

## Sources checked today (abstract or search-summary level)

- Barbieri–Sablik–Salo, *Self-simulable groups*, arXiv:2104.05141, abstract:
  https://arxiv.org/abs/2104.05141
- Durand–Romashchenko, *The expressiveness of quasiperiodic and minimal shifts of finite
  type*, arXiv:1802.01461, abstract: https://arxiv.org/abs/1802.01461
- Golan–Sapir, *On the stabilizers of finite sets of numbers in the R. Thompson group F*,
  arXiv:1605.05387, abstract: https://arxiv.org/abs/1605.05387
- Nekrashevych, *Finitely presented groups associated with expanding maps*,
  arXiv:1312.5654, abstract: https://arxiv.org/abs/1312.5654
- Nekrashevych, *Simple groups of dynamical origin*, arXiv:1511.08241, search summary of
  the abstract: https://arxiv.org/abs/1511.08241
- Clapham, *An embedding theorem for finitely generated groups*, Proc. LMS (3) 17 (1967)
  419–430, search-summary level only; the paper itself was not read:
  https://londmathsoc.onlinelibrary.wiley.com/doi/pdfdirect/10.1112/plms/s3-17.3.419
