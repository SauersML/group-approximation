# Audit: the "Invisible Quotients in Group Approximation" flagship plan

Date: 2026-08-23.  Subject: a two-message plan proposing a flagship paper built
around the split epimorphism `q: W -> G` that many approximation theories cannot
distinguish from an isomorphism, with the `A_5` one-relation theorem as the
opening and the `A_n` noncommensurable family as the climax.

## The headline theorems are real and in hand

Checked with `cairn why`; all four are ESTABLISHED with Lean artifacts attached
(`GroupApproximation/Algebra/VisibleQuotient.lean`,
`Sofic/LinearResidual.lean`, `Algebra/FiniteResidual.lean`):

* `compression-wreath-five-radicals-coincide` -- for `W_K = K^(G*/Gamma*) x| G*`,
  `R_K = Rad_MF = Rad_fd = Rad_lin = Rad_Bohr = Res_fin`, in the `Hom`-bijection
  form, for finite, residually finite, countable MF, `GL_d(F)`, `U(d)`, compact
  Hausdorff and norm-corona unitary targets.  Derivation runs through
  `compression-torsion-collapse` (scaled Kazhdan transport, corona commuting
  torsion lifts, Kazhdan coboundary collapse) and
  `doubling-quotient-residually-finite`.
* `simple-lamp-radical-one-relation` -- for a simple lamp the whole invisible
  kernel is one relation.
* `alternating-lamp-noncommensurable-family` -- established via
  `alternating-family-separated-by-radical`, from the five-radicals node plus
  `corona-finite-index-radical-heredity`.
* `profinite-twins-opposite-mf` -- profinite twins with opposite MF behaviour.

So the proposed §5, §6 and §7 rest on established nodes, not on aspiration.  The
plan is buildable as written.  Six live routes already consume the five-radicals
node, so it is load-bearing well beyond this paper.

## The opening theorem states one clause the graph refutes

The plan boxes:

> `W` is sofic, hyperlinear, and non-MF.

**The soficity clause is false in the graph, and the hyperlinearity clause is an
open target being attacked in the opposite direction.**

* `wreath-not-sofic` is ESTABLISHED from Kun--Thom (arXiv:2608.06222, Theorem A:
  `Gamma` infranormal but not normal in `G`, both Kazhdan, gives a nonsofic
  generalized wreath product) -- and `G*/Gamma*` is exactly such a pair.
* `a5-wreath-contains-binary-kun-thom-wreath` is ESTABLISHED: the `A_5`
  generalized wreath contains the binary Kun--Thom wreath, sitewise by an
  involution.  Soficity passes to subgroups, so `W_(A_5)` is **not sofic**.
* `simple-lamp-hyperlinear-recovery-forces-action-sofic` is OPEN, and the live
  route `nonhyperlinear-via-simple-lamp-action-recovery` aims to combine it with
  the established `coordinate-action-not-sofic` to prove `W_(A_5)` is
  **non-hyperlinear** -- which would answer the program goal.  Asserting
  hyperlinearity asserts the negation of a live target.

The likely source of the error is a genuine neighbouring node:
`wreath-sofic-not-mf` is ESTABLISHED and reads "sofic and not MF", but its
subject is the **sign-free mod-two quotient**, a different group.  Wired the
correction as `a5-compression-wreath-is-not-sofic`.

**This is upside, not damage.**  Nothing in the invisible-quotient theorem uses
soficity; deleting the clause costs the paper nothing.  The true status --
non-sofic, non-MF, hyperlinearity open -- makes the invisible kernel more
dramatic, and if the open route closes, `W_(A_5)` becomes the program's answer
group rather than a sideshow, which would change which paper this is.

The non-MF clause needs no separate citation: `Rad_MF(W) = A_5^(X) != 1` and an
MF group has trivial MF radical, so non-MF-ness is immediate from the flagship
theorem itself.

## The Grothendieck positioning: the second message corrects the first

The first message proposed selling the result as a Grothendieck cousin; the
second withdraws "Grothendieck pair" in favour of "Grothendieck-type
invisibility for approximation theories".  That is the right call, and the
reason is sharper than stated:

**Once `W` is not residually finite, the profinite half is automatic.**  Every
homomorphism to a finite group kills `Res_fin(W)` by definition, so
`Res_fin(W) = R` already gives `W^ = G^` and `Hom(G,F) = Hom(W,F)` with no
input from compression, property (T), or coronas.  Leading with "invisible to
every finite quotient" therefore sells the free end of the theorem.

The content is that the universally valid chain

```text
Rad_MF  subset  Rad_fd = Rad_Bohr  subset  Res_fin
```

collapses.  The inclusions are free (finite groups sit in `U(d)` and are MF;
Peter--Weyl equates the Bohr and finite-dimensional radicals; Malcev makes
finitely generated linear images residually finite hence MF).  The theorem is
that for `W_K` the smallest equals the largest -- i.e. the operator-norm corona
sees no more than a finite quotient does.  That is the sentence the abstract
should carry.  Wired as `invisible-quotient-is-not-a-grothendieck-pair`.

Before this ingestion the graph had **zero** nodes mentioning Grothendieck,
while the plan made the comparison load-bearing -- the recurring "load-bearing
everywhere, absent as a node" defect.  Now wired.

**Citation fidelity.**  Grothendieck 1970 and Bridson--Grunewald (Ann. of Math.
160 (2004) 359--373) are as described.  The attribution to
Jaikin-Zapirain--Lubotzky, *Some remarks on Grothendieck pairs*, is **not
confirmed**: the article exists (Groups Geom. Dyn. 19 (2025), those authors),
but its abstract concerns profinite rigidity and left/right Grothendieck
rigidity and says nothing about Bohr or proalgebraic completions.  Recorded as
an unverified scope note; nothing downstream leans on it.

**A free strengthening worth an hour.**  Grothendieck's theorem is an *if and
only if* between `u^` being an isomorphism and `Rep_A` restriction being an
equivalence for every nonzero commutative ring `A`.  The profinite half is
already in hand, so if the theorem applies here the paper gets a
representation-category equivalence at zero cost -- strictly stronger than the
`Hom`-bijections, since it compares morphisms and extensions.  The risk is
whether the equivalence direction needs residual finiteness, which `W_K` lacks.
Wired OPEN as `grothendieck-free-representation-category-equivalence`.

## Paper II claim, checked in passing

`defect-saturation-full-mf-radical` is ESTABLISHED and does deliver the full
package -- two-generated, finitely presented, torsion-free, property (T),
acylindrically hyperbolic, `Res_MF(G) = G`, with quotient heredity.  Its node
carries an explicit trust boundary: the Hull/Osin existence step is
source-verified and paper-level, not formalized, while defect saturation, full
MF residual, heredity and the CDE consequences are kernel-checked in
`TorsionFreeFullMFRadical.lean`.  The plan's proposal to supersede Hilbert-hotel
with this is supported.

## One process note

The plan says "Hilbert-hotel: delete."  Deleting nodes in this graph is not a
local act -- peers key `distinct_from` and `requires` on ids within the hour, and
a removed id is a hard error for every session.  Superseding is the safe move:
mark the Hilbert-hotel region superseded and retarget its routes, leaving the
ids resolvable.  No deletion was performed here.
