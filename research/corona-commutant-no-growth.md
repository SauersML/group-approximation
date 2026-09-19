---
rg: 2
id: corona-commutant-no-growth
kind: claim
title: Operator-norm relative commutants do not grow under the compression
root: true
refuted_by: corona-commutant-growth-witness
invalidates:
  - commuting-lamp-mf-detects-defect
  - literal-mark-quotient-detects-defect
  - literal-quotient-computes-mf-radical
distinct_from:
  commutant-no-growth: That claim is the finite-dimensional statement, proved by comparing dimensions of the two commutants; this one asks the same question in a norm matrix corona, where no invariant size exists.
  kazhdan-asymptotic-commutant-transport: That claim transports Hilbert--Schmidt asymptotic commutants and concludes in the 2-norm; this one is about exact operator-norm relative commutants inside the corona.
  commutant-projection-extraction: That claim asks for projections inside a relative commutant of a central mark; this one asks whether the relative commutant of the compressed Kazhdan image is larger than that of the Kazhdan image.
  relative-wall-commutant-growth: That established claim is the algebraic equivalence between a relative wall and growth of the relative commutant, valid in any target; this one asks whether the growth actually occurs in one specific non-tracial target, the norm matrix corona.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Let `Gamma` have property (T), let `iota : Gamma -> H` with
`t iota(Gamma) t^{-1} <= iota(Gamma)` for some `t in H`, let
`Theta : H -> U(Q)` be any corona representation, and put
`C = Theta(iota(Gamma))' cap Q`.  The compression gives

```text
C  <=  Theta(t) C Theta(t)^*  =  Theta(t iota(Gamma) t^{-1})' cap Q .
```

The claim is that this inclusion is always an equality.  The instances that
matter are `H = E`, `H = W/<zeta>` and `H = E/<w>`, with
`Gamma = Gbar`, `t = tau`.

**RESOLVED NEGATIVELY IN GENERAL; THE FORK WAS A FALSE DICHOTOMY
(2026-08-15).**  The negation of the general statement is established:
`corona-commutant-growth-witness` builds, over every residually finite
ambient with a strict finitely generated compression, a faithful
finite-quotient corona representation and a slow-phase unitary in the
compressed commutant but not the full commutant.  The instances this card
called "the single fork" are nevertheless decided — negatively — by a
different mechanism: the involutive collapse applies directly
(`commuting-lamp-quotient-not-mf`, `literal-mark-quotient-not-mf`), so
`unsquared-defect-mf-visible` fails and `u in Rad_MF(E)` without any
commutant-invariance input.  What survives of the dream is exactly the
projection-generated part: `corona-projection-collapse` proves the
relative commutant CANNOT grow by projections with commuting orbits, and
`spectral-component-motion-bound` shows any growth is confined to
connected spectral components — the slow wall's arc spectrum is not an
artifact but a necessity.  The group-element version of the dream is also
false: `infinite-cyclic-compression-lamp-mf` and
`mf-vs-tracial-radical-strict-gap`.  This claim can never be established;
the card is retained as the record of the question and for its
calibrations.

**This is the single fork.**  Granting it, `Theta(d) = Theta(t c t^{-1})`
lies in `Theta(t iota(Gamma) t^{-1})' cap Q = C`, hence commutes with
`Theta(iota(v_1))`, so `Theta(u) = 1` for every corona representation of
every such `H`.  Then `u` lies in `Rad_MF(E)`,
`unsquared-defect-mf-visible` fails, and both
`commuting-lamp-quotient-mf` and `literal-mark-quotient-mf` are **false**,
because the surviving image of `u` is a nontrivial element of `W/<zeta>` and
of `E/<w>` that no corona representation can detect.  If the claim fails, the
witnessing representation is exactly the model both open claims ask for.

**Scope: three open questions at once.**  Nothing in the statement uses the
affine base, so the same argument applies to any Kazhdan compressor pair.
Besides the two marked quotients it therefore decides
`kun-thom-wreath-weak-mf` — the commuting-lamp wreath
`(sum_{G/Gamma} C_2) semidirect G` of the Kun--Thom pair — negatively.  And
by `marked-quotient-mf-forces-commutant-growth` the converse holds for each:
MF of any of these groups *requires* the growth, witnessed by a single lamp.
So this claim is an exact hinge, not a one-way sufficiency.

## Ideas

**Compressor-free form** (from `relative-wall-commutant-growth`, cairn-wall).
Lemma 1 of `notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md` is purely
group-theoretic, so it applies to `U = U(Q)`: `Ad Theta(s)` carries
`C_{U(Q)}(Theta(Gamma))` *onto* `C_{U(Q)}(Theta(s Gamma s^{-1}))`.  Since
the set of `g` with `Ad Theta(g)(C) = C` is a subgroup containing `Gbar`, and
`V = <Gbar, tau>`, the claim is equivalent to:

> the relative commutant of the represented Kazhdan subgroup is invariant
> under `Ad Theta(V)`.

No compressor quantifier and no choice of `t` survives.  Scope note that must
travel with this reformulation (cairn-wall): the equivalence needs the
compression semigroup `P_Gbar` to *generate* the ambient group of the
invariance statement.  Here that group is `V = <Gbar, tau>`, so it is
automatic; restated for a larger ambient — `W/<zeta>` or `E` — the generation
hypothesis has to be re-checked, and without it only the one-way direction
survives, invariance implying no growth.  Two calibrations
from the same source: in the tracial branch the Pimsner--Popa index is a
conjugation-invariant strictly monotone size, which is why that branch
collapses, and `Q` carries no trace, so the invariant does not transfer; and
the analogous inclusion is genuinely proper in a metric ultraproduct of
finite groups (`kun-thom-clifford-cover-weakly-sofic`), so no purely
group-theoretic no-go can be valid — a proof must use something specific to
the operator-norm corona.

The same inclusion collapses in every category with a conjugation-invariant
strictly monotone size (`invariant-size-collapse`): finite groups by
`Nat.card` (`marked-quotients-not-lef`), finite-dimensional representations by
commutant dimension (`commutant-no-growth`), and the Hilbert--Schmidt
ultraproduct by Murray--von Neumann equivalence of the Kazhdan projection
(`kazhdan-asymptotic-commutant-transport`).  `Q` is stably finite but carries
no trace, and the transport argument only recovers a size after passing to the
adjoint corona, where the norm is the `2`-norm; that is precisely why
`corona-hs-radical-is-finite-residual` is a `2`-norm statement.

Two concrete attacks; the first has now been worked, and half of it is closed.

- **Stability.**  The uniform-stability form of this attack is **dead**:
  `corona-defect-is-not-uniform` shows a corona representation of an infinite
  group supplies only pointwise vanishing defect, never the uniform smallness
  that Ulam-type theorems hypothesize, and no choice of lifts repairs it.  The
  route `corona-commutant-no-growth-via-uniform-stability` is invalidated, and
  the coverage question for the affine group — unresolved at source level in
  `research/artifacts/glmr-2301-00476-verified.md`, since
  `Z^3 sd SL_3(Z)` is a lattice in a *non*-semisimple group — never needs to
  be settled.  What survives is the same reduction with **matricial
  stability** (Dadarlat, Adv. Math. 2021), which is stated precisely for
  lifting homomorphisms into the matrix corona.  Whether the affine Kazhdan
  group is matricially stable in the operator norm is the live question.

- **Averaging is not available at all.**  `kazhdan-projection-not-in-l1`: the
  Kazhdan projection is not in the image of `l^1(Gamma)`, and the averages
  converging to it in `C*_max` are not `l^1`-Cauchy.  An isometric action on a
  Banach space extends to `l^1` and no further without a Hilbertian structure,
  so `Ad Theta(p)` is undefined on `Q` and the projection onto the relative
  commutant cannot be produced by averaging in the operator norm.  This is why
  every (T) argument in this cluster passes to the adjoint corona first and
  ends in the `2`-norm, and it is the corona-side answer to what separates `Q`
  from a metric ultraproduct of finite groups.
**A consistency datum, explicitly not evidence** (cairn-wall).
`kun-thom-clifford-extension-not-weak-mf` is established in another lane by a
direct anticommutation argument, with no commutant-growth input: the
Kun--Thom Clifford extension has no operator-norm microstates at all.  That is
consistent with this claim holding — "no growth implies no MF" is the
contrapositive of `marked-quotient-mf-forces-commutant-growth` — but it does
**not** support it, because an independently proved "no MF" does not imply
"no growth"; the implication runs the other way.  Recorded so that two
independent negative results on a neighbouring group are not mistaken for
evidence about this hinge.

- **Construction.**  A counterexample needs a corona representation of
  `W/<zeta>` in which the represented base is not normalized by the
  represented shift.  By `corona-hs-radical-is-finite-residual` the growth
  must be carried on corners of vanishing normalized rank, and by
  `marked-quotients-not-lef` no exact finite model does it.

**Full consequence, recorded 2026-08-15.**  Granting the claim for every
compressor pair of `H`, every corona representation sends each compressed
centralizer element `Theta(t z t^{-1})`, `z in C_H(iota(Gamma))`, into
`Theta(iota(Gamma))' cap Q`; so every commutator `[t z t^{-1}, gamma]` with
`gamma in iota(Gamma)` dies in every corona representation, and the entire
compression-centralizer defect — not one marked `u` — lies in `Rad_MF(H)`.
The Hilbert--Schmidt analogue of exactly this consequence is kernel-checked
in `GroupApproximation/Sofic/IntrinsicCompressionMFRadical.lean`; this claim
would upgrade it from the 2-norm to the operator norm, deleting the corner
machinery for ordinary commutant defects in one stroke.  A second
sufficient meta-principle reaching the same endpoint without deciding this
hinge is `mf-invariant-corner-visibility`; to fire at `u` it additionally
needs tracial killing of `u` in every invariant corner, known today only
for the finite-normal and normal-Kazhdan corners, and its own card records
that it drifts toward MF-implies-hyperlinear strength.
