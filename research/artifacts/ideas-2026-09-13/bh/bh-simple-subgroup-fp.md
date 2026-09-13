# Idea lane: from a simple subgroup of a finitely presented group to a finitely presented simple group

Idea lane `bh-simple-subgroup-fp`, 2026-09-13. Target: `boone-higman-conjecture`.
Lens: the gap between "embeds in a simple subgroup of a finitely presented
group" (a theorem, carried here as `bht-trivial-normal-intersection-envelope`
and `boone-higman-thompson-simple-envelope`) and "embeds in a finitely presented
simple group" (the conjecture).

This is an exploration record. Nothing here claims to solve anything, and no
Cairn node is changed. Every kill test below was run now. The level of each
check is stated with it: source abstract, search summary, or repository node.

Dead routes already recorded on the root and not repeated: maximal normal
quotients of the envelope, Zorn on finitely normally generated kernels,
property (T) as Max-n, fixed Leavitt hosts, finite-ray shift compilers, and
BFFHZ action images of MIF cores.

## A1. Absorb relators by finitely many small-cancellation relators over a double

**Idea.** For `S <= Gamma` with `Gamma` finitely presented and `S` finitely
generated, the double `D = Gamma *_S Gamma` is finitely presented and contains
`S`. Try to add finitely many relators, chosen by small cancellation over the
amalgam, that force every nontrivial element to normally generate, while
keeping `S` embedded through the small-cancellation geometry.

**Would prove.** A universal compiler from the Boone--Higman theorem's chain to
a finitely presented simple container.

**Kill test.** If the resulting group is infinite and keeps a non-elementary
acylindrical action on a hyperbolic space (the Bass--Serre tree, or the coned-off
small-cancellation space), then it is acylindrically hyperbolic. Acylindrically
hyperbolic groups are SQ-universal, hence not simple.
- *Level:* read through a search summary of Osin's survey arXiv:1712.00814, not
  from source text.
- *Scope:* Minasyan--Osin arXiv:1310.6289 treats amalgams and HNN extensions in
  this setting (abstract read).

**Verdict: killed as a method, and it leaves a firewall.** Finitely many
relators must destroy every non-elementary acylindrical action of the container.
That removes exactly the geometric control that would keep `S` embedded. Any
relator-absorbing construction has to land outside the acylindrically hyperbolic
class, in Thompson-type, higher-rank or boundary-action territory.

## A2. Look for the container as a normal subgroup of the envelope

**Idea.** Take the finitely presented `P` of `bht-trivial-normal-intersection-envelope`.
Choose characters `chi: P -> Z` whose kernels are finitely presented (Bieri--Renz
Sigma-invariants), cut down to a simple finitely presented normal subgroup, and
push the input into it.

**Would prove.** The conjecture through finiteness properties of normal
subgroups, avoiding maximal kernels altogether.

**Kill test.** By that node, every proper normal subgroup `N` of `P` satisfies
`N ∩ Gamma = 1`. So the input lies in no proper normal subgroup of `P` (repository
node read at origin/main).

**Verdict: killed, with a firewall.** Inside any such envelope, a finitely
presented simple container of the input is never a normal subgroup. It must be a
quotient (the recorded dead Zorn route) or a non-normal subgroup `Gamma <= H <= P`.
No mechanism for the non-normal case is known.

## A3. NP-first split: a simple Birget--Olshanskii--Rips--Sapir theorem

**Idea.** Split the conjecture by word-problem class. Birget--Olshanskii--Rips--Sapir
(Annals 156 (2002), abstract arXiv:math/9811106 read) prove: the word problem of a
finitely generated group is in NP iff the group embeds in a finitely presented
group with polynomial isoperimetric function. Wagner, arXiv:2509.17841 (abstract
read), makes such embeddings quasi-isometric.

Proposed strictly easier subproblem: every finitely generated group with word
problem in NP embeds in a finitely presented **simple** group with polynomial
Dehn function. Build it by a Thompson-type tail over the S-machine envelope.
Evidence that tails can carry geometric complexity: Zaremsky, arXiv:2305.15176
(abstract read), builds finitely presented simple groups with at least
exponential Dehn function from Röver--Nekrashevych groups over self-similar
Baumslag--Solitar representations.

**Would prove.** The conjecture for every input with word problem in NP. That
would be a very large new class, since it contains every known structured case
with polynomial word problem. It would also give a geometric normal form for the
containers.

**Kill test.** Is the class split sharp or inconsistent? Take Birget
arXiv:1902.03852 (cited in `fp-simple-groups-with-arbitrarily-complex-word-problem`):
the word problem of `nV` is coNP-complete for `n >= 2`. By the theorem above,
if `nV` embedded in a finitely presented group with polynomial Dehn function,
its word problem would be in NP, and then NP = coNP. So polynomial-Dehn simple
containers can hold exactly the NP-word-problem inputs unless complexity classes
collapse. Nothing forces a collapse, so the subproblem is consistent. Simple
finitely presented groups with polynomial Dehn function do exist: `T` has
quadratic Dehn function (arXiv:2410.23088). This was seen through search results
only, not from source text.

**Verdict: survives.** It is a sharply posed, strictly easier subproblem, and
its novelty is unchecked. The cheapest next test: does some finitely presented
simple group with polynomial Dehn function contain `BS(1,2)`, or an S-machine
group with non-hyperbolic Dehn function?

## A4. Topological full groups with a known normal lattice as containers

**Idea.** For minimal effective expansive ample groupoids the derived full group
is simple, so the whole normal lattice is known and no Zorn step is needed.
Suppose the input embeds in a full group `[[G]]` that is finitely presented with
finite abelianization. Then the derived subgroup is a finitely presented simple
container.

**Would prove.** The conjecture through a universal groupoid host.

**Kill tests.**
1. Grigorchuk--Medynets, arXiv:1105.0719, abstract read verbatim: the commutator
   subgroup `[[T]]'` of a Cantor minimal `Z`-system "is infinitely presented".
   So the unbranched `Z`-subshift version never gives finite presentation.
2. `decidable-fp-groups-need-not-embed-in-rational-group`, a repository node read
   at origin/main: finite-state Cantor realizations cannot be universal.

**Verdict: unclear, and no new lane.** It survives only for expanding groupoids
that are not finite-state. That is the repository's shell-envelope program in
groupoid language, and no new universal mechanism came out of this lens.

## A5. Type (A) actions on S-machine envelopes

**Idea.** Keep the fp Higman or S-machine envelope `P` of the input and look
for a faithful type (A) action of `P`. Natural candidates are coset spaces of
machine subgroups coming from its HNN and amalgam structure. The twisted
Brin--Thompson envelope then gives a finitely presented simple container
(`boone-higman-via-permutational-boone-higman`).

**Would prove.** Permutational Boone--Higman for machine envelopes, hence the
conjecture.

**Kill test.** Fournier-Facio--Kropholler--Lyman--Zaremsky, arXiv:2506.02319,
abstract read: for all groups of finite virtual cohomological dimension and all
countable linear groups, every oligomorphic action on an infinite set has a finite
subset whose stabilizer is not of type FP_infinity. This obstructs finiteness
properties of twisted Brin--Thompson groups. The obstruction sits at the
FP_infinity level, while finite presentation of the container needs much less.

**Verdict: unclear.** The next test is to read which finiteness level the
BFFHZ type (A) definition needs of point stabilizers. If it is only finite
generation, arXiv:2506.02319 does not bite.

## Summary

| # | Approach | Verdict |
|---|---|---|
| A1 | Small-cancellation relator absorption over a double | killed; firewall: the container is not acylindrically hyperbolic |
| A2 | The container as a normal subgroup of the envelope | killed; firewall: never normal inside the envelope |
| A3 | NP-first simple Birget--Olshanskii--Rips--Sapir theorem | survives; sharp and consistent with known complexity; novelty unchecked |
| A4 | Full groups with known normal lattice | unclear; overlaps the shell routes |
| A5 | Type (A) actions on S-machine envelopes | unclear; the FP_infinity obstruction may not bite at fp |
