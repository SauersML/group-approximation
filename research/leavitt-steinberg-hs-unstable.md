---
rg: 2
id: leavitt-steinberg-hs-unstable
kind: claim
title: The binary Leavitt Steinberg cover is normalized-HS unstable
distinct_from:
  leavitt-steinberg-hs-stable: These are mutually exclusive branch selections for the same explicit group.
  hyperlinear-wreath-model: This asks only for one nontrivial tracial-ultraproduct image of the Steinberg cover; the other asks for a faithful hyperlinear model of a wreath candidate.
  hs-expander-block-decomposition: That is the general Kazhdan-group decomposition whose proof would select the opposite branch; refuting it does not by itself select this one.
artifacts:
  - docs/ATLAS_HS_CRITERION.md
  - docs/NOTEPAD.md
---

Construct a normalized-HS asymptotic representation of
`St_5(L_(F_2)(1,2))` that cannot be corrected to genuine finite-dimensional
representations.  Since every such genuine representation is trivial, it
is enough to make the finite quotient relators tend to `1` in exact atlas
representations while one fixed word stays a positive distance from `1`.

## Ideas

**The "one witness suffices" reduction is this claim, not a decomposition of
it.**  Because `U` is minimally almost periodic, the only genuine
finite-dimensional representation is trivial, so instability is *by
definition* the existence of one almost-representation family bounded away
from `1`.  Equivalently, one nontrivial homomorphism `U -> U(R^omega)`, one
nontrivial Connes-embeddable trace on `U`, or one exact-atlas sequence
satisfying `(A)`--`(B)` of `docs/ATLAS_HS_CRITERION.md`.  These are already
recorded as the content of `leavitt-steinberg-hs-stability-fork`; restating
them as a sub-claim buys nothing.  The genuine sub-problems are the
constructions, and the ones that are closed are listed in the fork's
artifacts: ring-first Leavitt microstates (`2-sqrt(3)` contraction floor,
kernel-checked), hyperfinite and amenable-character models, monomial and
block-monomial relative unitaries, Haar and asymptotically free ensembles,
bounded internal complexity, and the entire additive-root/Hellinger program.

**The construction is reduced to finite matrix feasibility, and the fences
are sharp.**  `docs/ATLAS_HS_CRITERION.md:196-217` proves the one-witness
exact-atlas certificate and `:247-253` its converse; `:286-298` makes the
variables finite -- integer multiplicity vectors per chart, finitely many
relative unitaries `V_i`, and the common size `d` -- and `:357-407` upgrades
this to a ratio criterion under which sparse seeds suffice provided relator
defects vanish faster than the survivor.  `docs/EXPLICIT_LEAVITT_ATLAS.md:452-456`
states the endgame as a sequence of compact one-unitary optimizations.  Two
fences bound the search: `steinberg-hyperfinite-hs-stable` forbids any
witness with hyperfinite, AF, amenable-factor or character-approximation
limit, and `leavitt-multiplicative-trace-floor` together with
`docs/NOTEPAD.md:22096-22133` forbids every ring-first construction --
square-matrix Fock, Toeplitz, leaf-truncation, polar-correction, direct-sum
-- in normalized HS and not merely in operator norm.  The same passage
(`:22135`) declines to conclude stability from the floor, correctly.

**Why the nonsoficity of `Q` is not evidence against this branch.**  The
source of the nonsoficity theorem says so itself, verbatim and identically
in both released versions: "Thus every sofic group is hyperlinear [Pes08,
Theorem 3.3], but Theorem 1.1 does not determine whether `L_(F_2)(1,2)^x` is
hyperlinear."  The structural reason is now pinned down precisely.  Of the
three steps of the one-sided-compression argument, two transcribe to a
finite tracial algebra unchanged -- see
`hs-block-decomposition-to-steinberg-stable`, where the conservation
identity becomes trace preservation under unitary conjugation and the
majority matching becomes `sum_i tau(f e_i f) <= tau(f)`.  The only step
with no tracial analogue is Kun's expander decomposition, and its
permutation input is not a *theorem* about Kazhdan groups but the ambient
fact that a permutation model acts on a set, so its invariant algebra is
atomic before any hypothesis is used.  A nonsoficity proof that leans on
atomicity is exactly the kind that leaves hyperlinearity open.

**The compression pattern alone is hyperlinear-compatible, explicitly.**
The full hypothesis pattern of the criterion, minus property `(T)`, is
realized inside an amenable group.  In `G = Z wr Z = A semidirect <t>` with
`A = directSum_(n in Z) Z` and `t` the shift, take
`Gamma = directSum_(n>=0) Z`, `J = <e_(-1)> = Z`.  Then
`t Gamma t^(-1) = directSum_(n>=1) Z` is a **strict** subgroup of `Gamma`,
`G = <Gamma,t>`, `[Gamma,J]=1`, `Gamma cap J = 1`, and
`t J t^(-1) = <e_0> <= Gamma`.  `G` is amenable, hence sofic and hyperlinear,
and the conclusion of the criterion holds harmlessly because `J = Z` is LEF.
So no argument that uses only the compression data can obstruct
hyperlinearity: property `(T)` of `Gamma` and `G`, together with failure of
LEF for `J`, carries the entire theorem.

**The escape is proved sharp elsewhere in this graph.**  At every finite
level a compression is an equality by counting -- `invariant-size-collapse`
formalizes exactly this for cardinality, finrank, `Nat.card` and Haar
measure -- and the `II_1` branch survives only because the trace is
refinement-blind, which `trace-blindness-sharpness` establishes is not
repairable.  Strictness of a compressed relative commutant is therefore a
purely ultraproduct phenomenon.  That is precisely the room a hyperlinear
model needs, and it is the room a permutation model does not have.

**The honest counterweight.**  The permutation analogue of this fork, for
this same group, has already been decided -- on the stable side.  `U` is
`P`-stable: its only genuine finite permutation representations are trivial
(a nontrivial one would give a nontrivial finite quotient, contradicting
minimal almost periodicity), so `P`-stability is equivalent to nonsoficity,
which is proved.  The prior "no such exotic group has ever been produced"
was therefore already wrong once, for this exact group, in the neighbouring
metric.  Anyone weighing the two branches should apply that discount.

**The reframing that still tilts the balance.**  By
`steinberg-hs-stability-equals-nonhyperlinearity`, the fork is an
equivalence: `U` is HS-stable if and only if `U` has no nontrivial
hyperlinear quotient, if and only if `Q` is nonhyperlinear.  Consequently
the opposite branch is not a stepping stone toward a nonhyperlinear group --
on it, `Q` *is* one -- so no route to `leavitt-steinberg-hs-stable` can be
cheaper than producing the first nonhyperlinear group known, and `U` would
be the first infinite Kazhdan group known to be HS-stable, every Kazhdan
group of settled status being residually finite, hence sofic, hence
hyperlinear, hence unstable by Becker--Lubotzky Theorem 1.3(ii).  This
branch, by contrast, asks for a construction in a category where
constructions of this shape routinely exist.  Net assessment as of
2026-08-14: this branch is favoured, but weakly, and the discount above is
real.

One phrasing trap, since the equivalence is easy to overstate.  Condition 3
is nonhyperlinearity of `Q`, not of `U`.  "`U` nonhyperlinear" forbids only
an injective homomorphism into a tracial matrix ultraproduct, whereas
stability forbids every nontrivial one; the gap between them is exactly the
noninjective homomorphism this branch is trying to construct, whose central
kernel makes a proper central quotient of `U` hyperlinear while leaving `U`
itself possibly nonhyperlinear.

**Neighbouring stability results, for calibration.**  Two 2026 data points
bound how much the flexible/strict distinction can be worth.
Lubotzky--Salomon (arXiv:2607.17578) exhibit `Z^2` as flexibly stable but not
stable in the operator norm, the first such group -- so the gap is genuinely
crossable, and a flexible variant of this claim is a strictly weaker target,
which `docs/NOTEPAD.md:22593-22596` already notes would suffice.
Becker--Chapman proved uniform flexible stability **in permutations** for all
amenable groups (recorded in Kun--Thom arXiv:1901.03963v3 §5); that is the
state of the art on the flexible side and it does not reach this fork,
because `U` is as far from amenable as a group gets.
