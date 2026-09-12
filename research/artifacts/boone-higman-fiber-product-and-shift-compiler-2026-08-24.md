# Boone--Higman: two reductions that discharge simplicity, 2026-08-24

An external attempt on the Boone--Higman conjecture was handed to this
session.  It does **not** prove the conjecture, and its author says so: the
last finite-presentation step is unproved, and writing it as solved would
assume essentially the missing theorem.  What it does contain is two
reductions worth carrying, both of which route the conjecture through
Zaremsky's twisted Brin--Thompson machinery and both of which **never ask any
group to be simple**.  This file records what was checked, what was
corrected, and what was declined.

## A. Sources read this session

All four were retrieved and read on 2026-08-24.

**A.1 Zaremsky, *Finite presentability of twisted Brin--Thompson groups*,
arXiv:2405.18354.**

Type (A), verbatim:

> "(A): The action is faithful, the group `G` is finitely presented, each
> `Stab_G(s)` for `s in S` is finitely generated, and there are finitely many
> `G`-orbits of two-element subsets of `S`."

Theorem A, verbatim:

> "Let `G` be a group acting faithfully on a set `S`.  Then the twisted
> Brin--Thompson group `SV_G` is finitely presented if and only if the action
> of `G` on `S` is of type (A)."

Corollary B, verbatim:

> "Any subgroup of a group admitting an action of type (A) has solvable word
> problem and satisfies the Boone--Higman conjecture."

Proposition 5.3, verbatim:

> "Every finitely presented, strongly shift-similar group admits an action of
> type (A), and so in particular has solvable word problem and satisfies the
> (permutational) Boone--Higman conjecture."

Definition 5.2 gives shift-similar (`psi_j(g) in G` for all `g in G`, `j in
N`) and strongly shift-similar (each `psi_j|_G` surjective), with
`psi_j(g) = s_{g(j)}^{-1} . g|_{N \ {j}} . s_j`.

Theorem A was already in this graph as
`twisted-brin-thompson-finite-presentation-criterion`, read 2026-08-17.
Corollary B and Proposition 5.3 were not, and Corollary B is the statement
the routes actually consume, because it is the one that descends to
subgroups.

**A.2 Mallery--Zaremsky, *Houghton-like groups from "shift-similar" groups*,
arXiv:2202.00822, to appear J. Comb. Algebra.**  Theorem 3.28, verbatim:

> "For any finitely generated group `Gamma`, there exists a finitely
> generated strongly shift-similar group `G <= Sym(N)` such that `Gamma`
> embeds as a subgroup of `G`."

The construction embeds `Gamma` in `Sym(N)` with all generators of
half-finite support (acting on the even numbers) via an arbitrary bijection
`nu : Gamma -> N`, then adjoins `E_2`, the eventually 2-periodic
permutations.  The source records that `nu` is an arbitrary choice.  This
graph writes the result `E_nu(P)`; **that notation is local and is not the
source's**.

**A.3 Baumslag--Bridson--Miller--Short, the 1-2-3 theorem.**  Located through
the subdirect-product literature (arXiv:1107.2590, arXiv:1302.2745), not from
the primary paper: for `1 -> N -> T -> Q -> 1` with `N` finitely generated,
`T` finitely presented and `Q` of type `F_3`, the fibre product `T x_Q T` is
finitely presented.  An asymmetric strengthening is due to
Bridson--Howie--Miller--Short.

**A.4 Clapham (1967), Proc. LMS (3) 17, 419--430.**  Every finitely generated
group with solvable word problem embeds in a finitely presented group with
solvable word problem.  Bibliographic data confirmed; primary not read.  It
was already used in the prose of
`boone-higman-via-finitely-presented-simple-ring-quotient` and in section D.4
of `boone-higman-audit-2026-08-17.md`, without a node.  It has one now.

## B. The fiber-product lemma, re-derived

Verified line by line, not taken on trust.  For `1 -> N -> T -pi-> Q -> 1`
and `Gamma = T x_Q T`, the rule `(a,b) . x = a x b^{-1}` is a well-defined
transitive action on `N` with `Stab_Gamma(1) = Delta T`, ordered-pair orbits
in bijection with `T`-conjugacy classes of `N`, and kernel `Delta C_T(N)`.
Proof in `fiber-product-conjugation-action-lemma`.

Three things the source did not draw out, all cheap and all recorded as
screens on the open claim:

* `Z(N) <= C_T(N)`, so clause `C_T(N) = 1` forces `Z(N) = 1`.
* Conjugate elements have equal order and the order function factors through
  a finite class set, so `N` realizes only finitely many element orders.
  **This does not force finite exponent** -- an early draft of this note said
  it did, which is wrong for a group with elements of infinite order, and
  groups with finitely many conjugacy classes and elements of infinite order
  exist.  It forces finite exponent only when `N` is torsion.
* If `N` is finite then `C_T(N) = 1` embeds `T` in `Aut(N)`, so `T` is
  finite.  Any application to an infinite group needs `N` infinite.

**Correction to the source's attribution.**  The source invokes "the
asymmetric 1-2-3 theorem".  Both fibre-product factors here are the same
group `T`, so the symmetric 1-2-3 theorem of
Baumslag--Bridson--Miller--Short is what is used.  The asymmetric version is
not needed and is not cited by the graph.

## C. What the two reductions are

**C.1 Fiber-product criterion.**  `universal-fiber-product-data-for-word-problem-groups`
plus `boone-higman-via-fiber-product-criterion`.  Given `G` finitely
generated with solvable word problem, find `T` finitely presented containing
`G` and `N <| T` finitely generated with `T/N` of type `F_3`, `C_T(N) = 1`
and finitely many `T`-conjugacy classes in `N`.  Then `T x_Q T` is finitely
presented by 1-2-3, acts on `N` with type (A) by the lemma, and Corollary B
finishes.

The sharpest special case is `N = T`: *every finitely generated group with
solvable word problem embeds in a finitely presented group with trivial
center and finitely many conjugacy classes*.  That version needs no 1-2-3
theorem at all.  It is recorded inside the open claim rather than as a second
route, because it strictly implies the general one and a second route would
prove the same target by the same argument -- the failure mode this
repository has hit before.

**C.2 Shift--Higman compiler.**  `shift-higman-compiler` plus
`boone-higman-via-shift-higman-compiler`.  If `P` is finitely presented with
decidable word problem then some `nu` makes `E_nu(P)` finitely presented.
Chain: Clapham, then the compiler, then Theorem 3.28's "strongly", then
Proposition 5.3, then Corollary B.  Every step but the compiler is in print.

## D. The decidability check, and why it is the useful part

`compilers-cannot-drop-the-decidability-hypothesis`, with two parts:

(a) `E_nu(P)` finitely presented `=>` `P` has solvable word problem, via
Proposition 5.3 and Corollary B.  So a finitely presented `P` with unsolvable
word problem has no finitely presented envelope for any `nu`.

(b) The fiber-product data `=>` `T` has solvable word problem, via the lemma,
1-2-3 and Corollary B applied to `Delta T <= Gamma`.

The source states (a) as a sanity check.  Both are recorded because they
constrain the *shape of a proof*: no argument that manipulates a finite
presentation uniformly can establish either compiler, since such an argument
would apply to Novikov--Boone's group.  The decidability algorithm has to be
consumed, and in the shift lane the only place it can be consumed is the
choice of `nu`.

The `N = T` instance of (b) is proved here without any citation:
`conjugacy-finite-recursive-presentation-solvable-wp`, by complementary
enumeration -- the word problem is r.e., and so is its complement, because
"conjugate to `g_i`" is r.e. for each of finitely many class representatives
and every non-identity element is conjugate to one with `i >= 2`.  That is a
four-line check on the strongest instance of a conclusion the rest of the
region imports, and it is the reason to trust the imported form.

## E. Attacks declined, with reasons

* **Hide a non-faithful action upstairs.**  Pass to a finitely presented
  cover of an actor with the right orbit data but a kernel.  Fails on
  faithfulness, which is the type (A) clause that supplies simplicity of
  `SV_G`; the cover's action has kernel containing the covering kernel.
  There is no version of the criterion in which the kernel is harmless.
  Recorded in the open claim's `## Attempts`, not as a node, because the kill
  is that the imported theorem does not apply rather than a theorem of its
  own -- and because the graph already carries the correct handling in
  `boone-higman-via-bffhz-action-image`, which quotients by the action kernel
  and pays with an open finite-presentability claim about the quotient.
* **Wreath / Houghton envelopes to buy finite pair-orbits.**  Removes
  positional invariants, leaves base-group label invariants, so pair orbits
  stay infinite.  Recorded in `## Attempts`.
* **Andre--Guirardel sharply 2-transitive groups with property (T).**  The
  source offers these as a supply of spectacular orbit structure.  Declined
  as a node: the relevant literature was **not** verified this session, and
  the reason the idea fails is in any case that the criterion also needs
  finite presentability of the actor, which no such construction is claimed
  to supply.  Writing a node would put an unread citation on the graph to
  record a dead end, which is the wrong trade.
* **Claiming the conjecture.**  Declined by the source's own author and
  declined here.  Neither open claim is proved, and neither is known to be
  weaker than the conjecture in any formal sense; what they remove is the
  requirement to construct a simple group, not the difficulty.

## F. Relation to the existing region

The graph's earlier Boone--Higman lanes
(`boone-higman-via-ck-maximal-kernel`,
`boone-higman-via-finite-bi-index-envelope`, the ring lanes) all pass through
a group that must be shown simple or through a finite-normal-generation
condition on a maximal normal subgroup.  The two routes added here do not.
The bi-index route is the closest relative: it also ends at Zaremsky's
criterion, but through the coset action of the Chatterji--Kassabov envelope
on `Gamma/S`, with a double-coset finiteness as its open input.  The open
inputs of the three routes are about three different objects, and no
implication among them was found.
