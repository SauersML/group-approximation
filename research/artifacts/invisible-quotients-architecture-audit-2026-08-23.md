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

## CORRECTION: the opening theorem's soficity clause is right, and my first reading was wrong

An earlier pass of this audit asserted that the plan's box -- "`W` is sofic,
hyperlinear, and non-MF" -- was refuted by the graph, and landed an ESTABLISHED
claim `a5-compression-wreath-is-not-sofic` saying so.  **That was a group
mismatch and has been withdrawn.**  The claim and its route are removed and
replaced by `wreath-soficity-is-decided-by-the-base-pair`.

The graph carries the wreath construction over **two different compression
pairs**, and the soficity verdict flips between them:

* **Kun--Thom Laurent pair** -- `Gamma = EL_r(R_+)`,
  `G = EL_r(R) x| SL_d(Z)`.  `wreath-not-sofic` is established here, and
  `a5-wreath-contains-binary-kun-thom-wreath` extends it to `A_5` lamps.  Its
  body says "for the pinned Kun--Thom action", so its scope is this pair.
* **Affine doubling pair** -- `G* = (Z[1/2]^3 x| SL_3(Z)) x| Z` with the
  doubling stable letter.  This is the pair every radical theorem uses:
  `wreath-compression-mf-radical` says "the doubling family",
  `doubling-quotient-residually-finite` writes `G*` out, and
  `compression-wreath-five-radicals-coincide` is stated over `G*/Gamma*`.  Over
  this pair the telescope-window structure **restores soficity**:
  `wreath-sofic-not-mf` is established, and its own body draws the contrast --
  "the same wreath construction over the Laurent pair is NOT sofic, while over
  the affine/doubling pair the telescope structure restores soficity ...
  soficity of the wreath is a property of the base pair's finite-window
  geometry, not of the wreath shape."

The flagship `W` lives over the affine pair.  Moreover the established
`simple-lamp-radical-one-relation` states the plan's sentence outright: adding
`r = 1` turns "a **sofic** non-MF group into a residually finite MF group", with
`r` the lamp carrying `(1 2)(3 4)` at the base site.  **So the plan's soficity
clause is the graph's own established reading, and the correction was the
error.**

Two residual notes that survive the withdrawal, and are the useful part:

* *Hyperlinearity is still not background.*  The open target
  `simple-lamp-hyperlinear-recovery-forces-action-sofic` and the route
  `nonhyperlinear-via-simple-lamp-action-recovery` are stated over the
  **Kun--Thom** pair, so they are not aimed at the flagship group and do not
  contradict the plan.  But they are also not evidence *for* the plan's
  hyperlinearity clause, which needs its own citation over the affine pair
  before it is boxed.
* *The trap is real and now has a node.*  `wreath-not-sofic` warns in its own
  body against "exactly the kind of group-mismatch the doctrine exists to
  prevent", and this audit committed it anyway, on main, inside fifteen
  minutes.  The distinction previously lived only in `distinct_from` prose;
  `wreath-soficity-is-decided-by-the-base-pair` makes it a first-class object.

The non-MF clause still needs no separate citation: `Rad_MF(W) = A_5^(X) != 1`
and an MF group has trivial MF radical.

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

collapses.  Most inclusions are free (finite groups sit in `U(d)` and are MF;
Malcev makes finitely generated linear images residually finite hence MF).  The
Bohr column is the exception and is worth knowing before drafting: in this
repository `five_radicals_eq` carries a leading binder
`(hPW : SeparatesPoints)`, and the unconditional companion
`five_radicals_eq_profinite` restricts to profinite targets.  So the compact
column of the boxed five-radical equality is currently **conditional on one
named classical input**, exactly the Peter--Weyl separation statement the plan
already says it is willing to formalize -- and the repo has isolated which
statement that is (`research/artifacts/peter-weyl-separation-core.md`).  The
theorem is
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
