---
rg: 2
id: phase-safe-toric-gap-game-exists
kind: claim
title: Some finite two-player toric game has a commuting/finite-dimensional gap whose scalar phase survives normal closure
refuted_by: normal-phase-safe-toric-games-have-qa-one
artifacts:
  - research/artifacts/published-nonhyperlinear-shortcut-audit-2026-08-21.md
distinct_from:
  phase-safe-toric-gap-implies-nonhyperlinear: that is the proved implication from such a game to a nonhyperlinear group; this is the missing object itself, and it is where all the difficulty sits
  hyperlinear-nonsofic-group: that asks for a hyperlinear group failing soficity; a witness here goes the other way and produces a nonhyperlinear group
---

**REFUTED.**  The proposed missing object was one finite two-player torically
determined game `Gcal` with

1. finite phase group `B`;
2. `omega_qa(Gcal) < 1`;
3. the scalar phase surviving the normal closure of the clauses,
   `N ∩ B = {1}`.

By `phase-safe-toric-gap-implies-nonhyperlinear`, such a game gives an
explicit finitely presented nonhyperlinear group.  Item 3 may be replaced by
the sufficient certificate "a perfect tracial model of the *full* toric
universal game algebra".

`normal-phase-safe-toric-games-have-qa-one` proves that item 3 already forces
`omega_qa=1`: normal closure centralizes the two player components of every
clause, phase safety makes their scalar labels a consistent abelian
character, and that character splits into a perfect product state which is
approximable by one-player RFD models.  Thus the three requested properties
cannot coexist.  The attempts below are retained as the historical audit.

Two structural constraints are already proved and any candidate must satisfy
them: `H = <h_i>` must be infinite, and its projection to the game group must
have infinite index.  Finite or finite-index clause subgroups admit an induced
finite-dimensional representation with a distinguished vector satisfying every
clause, which forces `omega_qa = 1`.

## Attempts

**Compile a `MIP^*=RE` game.**  `MIP^*=RE` (arXiv:2001.04383) supplies finite
two-player games separating commuting from finite-dimensional correlations.
Where it dies: no verified compiler turns one of those games into a torically
determined game while preserving both the perfect gap and phase-safe normal
closure.  Watts--Helton--Klep supply the exact subgroup criterion
(`H ∩ B = {1}`), not the compiler, and the subgroup criterion is strictly
weaker than what is needed -- `C_2 x A_5` with `H = <ba>` has `H ∩ <b> = {1}`
while `b` lies in the normal closure of `H`.

**Wait for perfect completeness on the LCS side.**  Taller--Vidick's
RE-hardness theorem for linear-constraint-system games (arXiv:2507.22444) has
completeness `1 - epsilon`, and the authors note explicitly that reaching
perfect completeness would already imply a nonhyperlinear group.  So this
route is *at least as hard* as an open problem the LCS community has named;
it is not a shortcut past it.  The gain from the toric formulation is that
full LCS syntax is not logically necessary -- normal toric syntax, or merely a
phase-safe normal-closure certificate, suffices -- so the search space is
wider than "perfect LCS or nothing".

**2025--2026 static-game and gadget audit.**  Lin, arXiv:2510.07162,
Theorem 6.15 does supply a finite synchronous game with `omega_co=1` and
`omega_*<=1/2`; it supplies neither toric phase safety nor LCS solution-group
syntax.  Culf--van Dobben de Bruyn--Zeman, arXiv:2604.01408, characterize
robust commutativity gadgets, but their `qa`/`qc` gadget-class separation is
explicitly conditional on a nonhyperlinear group.  Thus neither theorem
constructs the object requested here.

The source-specific symmetry audit is now exact:
`lin-gap-wrappers-retain-oracular-atlas-holonomy` shows that Theorem 6.15 is a
promise-problem theorem, not one canonical answer-transitive game.  In its
oracular completeness form, the joint projections on sampled pairs form the
same compatible projection atlas as the BCS route.  Balance and conditional
linearity concern the sampling distribution; anchoring adds deterministic
leaves; parallel repetition retains an anchored copy of the prior incidence
diagram.  None supplies an internal scalar phase or block-escaping overlap
word.

**Use synchrony to get normality for free.**  Dead.  For a synchronous game
the perfect strategies are tracial states on the one-player synchronous
algebra (Paddock--Slofstra, arXiv:2310.07901), and it is tempting to argue a
trace vector fixed by the clauses is fixed by their conjugates.  The toric
clauses live in the *full two-player* universal game group; passing to the
one-player trace moves the second player's operators to an opposite algebra
and reverses word order there, so it does not identify the normal closure of
the two-player clauses with the trace-kernel ideal of the synchronous algebra.

Details and the finite counter-model for the subgroup-versus-normal-closure
gap: `notes/TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md` §§3-6.

**Projective-kernel phase mining.**
`boolean-predicate-central-phase-word` now supplies an exact finite `2`-group
word for every fixed nonlinear predicate. The source-engineering claim
`bcs-projective-kernel-phase-compilation` asks for that word to act as `-I` in
the full tracial model while its readers preserve the violation family.
`phase-safe-toric-via-projective-kernel` is the resulting live route. A local
phase calculation without a full universal-algebra model is rejected because
it does not prove normal-closure survival.

**Property FD / reversible-ancilla audit.**
`toric-gap-is-a-relative-fd-central-word-face` proves the exact state-space
criterion.  A toric gap is failure of finite-dimensional approximation on the
entire clause-character face, not merely nonapproximation of one induced
vector state.  Separate one-player RFD does not rule this out because the
two-player algebra is a maximal tensor product and can fail RFD (already for
`F_2 x F_2` after the negative solution of Connes embedding).  Conversely,
local finite reversible packets do not solve it: forbidden selector types
survive by induction.  Under normal phase safety every clause
`beta_i a_i b_i` centralizes `a_i` in the Alice image and `b_i` in the Bob
image, and the quotient has the exact central-product presentation `(RTF6)`.
Thus the surviving compiler target is a robust **central-word state-face**
compiler, not an ordinary local reversible circuit.

**Finite spherical root / Hecke packet.**  The strongest local version works:
for `H_R=(C_2)^R semidirect Sym(R)` and the coordinate character of
`K_R=(C_2)^R semidirect Stab(r_0)`, the induced spherical module is exactly the
irreducible tautological signed-permutation answer type.  But its scalar root
clauses are phase-unsafe.  Conjugacy moves a `+1` coordinate lamp to the
`-1` root lamp, so the normal closure contains the bare nontrivial scalar.
`spherical-root-type-selection-is-phase-unsafe` proves the general invariant-
extension criterion and this explicit collision.

**Extraspecial spin packet with private letters.**  Also blocked in its direct
form.  Every noncentral Pauli word `p` has `[p,x]=J`; normal toric
groupification centralizes each player clause word and therefore kills `J`.
Wrapping `p` as `t^(-1)pt` only conjugates the commutator witness.  See
`extraspecial-spin-predicate-centralization-kills-phase`.  A more elaborate
private-letter cycle remains admissible only if every clause word avoids
normally generating `J` through its commutators, a condition which must be
checked before state-vector completeness.

**Infinite malnormal character face.**  This does not survive the two-player
product geometry.  `two-player-product-has-no-proper-nontrivial-malnormal-subgroup`
proves that every nontrivial malnormal subgroup of `G_A x G_B` is the whole
product.  Hence a Cohen--Lyndon/free-normal-closure root cannot provide the
needed infinite-index clause face.  Any surviving infinite subgroup must be
highly non-malnormal and meet the full relative-FD face criterion above.

**Raw GNS projective kernel / Hahn--Banach.**  The projective kernel of a
tracial non-CE state is automatically normal and its scalar character is
phase-safe, but it does not inherit the finite-dimensional gap.  Its character
face is the whole state space of a twisted quotient and may contain unrelated
finite-dimensional representations.  Locally, group-word eigenvalue equations
see only the affine hull of a Boolean answer support, whereas the losing
projection sees the nonlinear support itself.  This exact obstruction is
proved in `non-ce-trace-does-not-promote-to-subgroup-character-gap`.

**Finite-phase monomial linking algebra.**
`finite-phase-monomial-game-algebra-dictionary` gives a narrower intermediate
language than LCS: order-`s` quantum-reflection entries, their exact Fourier
projection resolution, and one relation `uA=Bu`.  Harris first replaces the
fixed synchronous non-CE game by an equal-size bisynchronous game without
changing its algebra.  The live route
`phase-safe-toric-via-monomial-game-compiler` then has exactly two new gates:
realize that square game algebra as a finite-phase monomial matrix-pair
algebra, and groupify its existing gap while proving phase-safe normal
closure.  No classicalization of the monomial symmetry is used.
