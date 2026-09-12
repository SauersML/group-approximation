# The peeling boundary: local-bijection own-block rows, surjunctive tails, and where strictness lives

Lane `gk-p-tails`, 2026-09-12. Handwritten proofs; no computation. Supports the
Cairn claims `own-block-local-bijection-rows-peel`,
`peeling-to-surjunctive-memory-tail-forces-surjectivity` and
`strict-three-factor-needs-noninvertible-own-block`.

This continues `offset-corrected-peeling-2026-09-12.md` (offsets move into the
tail) and `three-factor-audit-and-controlled-feedback-2026-09-12.md` (the
peeling criterion and its three boundaries B1/B2/B3). Three questions were
open there:

1. which corrected tails are *known* surjective;
2. can peeling reach own-block nonlinear rows (boundary B3);
3. exactly where can strictness sit in the three-factor normal form.

The answers below: peeling extends to every own-block row that is a *local
bijection*, whether or not it is linear; a corrected tail whose rule reads only
a *surjunctive subgroup* is surjective; and a strict three-factor automaton
must, in every ordering, expose a row whose own-block map is **not** a local
bijection, the minimal cases of which are exactly the two direct-finiteness
families B1 and B3.

## 0. Setting and conventions

As in the two predecessor artifacts. `G` is any group, `R` a finite ring, the
tracks are grouped into blocks `X_1,...,X_r` with block `a` over `R^{d_a}`, and
all maps are cellular automata on the product full shift. A *local function of
`Y`* reads finitely many addresses of the blocks named `Y`, uniformly in the
group position. For a block `X` with the others written `Y`, a row of the
automaton in block `X` has the shape `row(X,Y)`. We use throughout:

* **(FIB)** `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`: a
  finite-memory map `D(Z,Y) = (Z, T_Z(Y))` that fixes the certificate `Z` is
  bijective iff it is injective and one fiber `T_{Z_0}` is bijective, and it is
  surjective iff injective and one fiber is surjective.
* **(SUB)** `surjunctivity-passes-to-subgroups`: a cellular automaton over `G`
  whose memory lies in a subgroup `H` acts on each left coset of `H` as a copy
  of an automaton over `H`; so over `G` it is injective (resp. surjective) iff
  its `H`-copy is, and a subgroup of a surjunctive group is surjunctive.

## 1. Own-block local-bijection rows

Call a row `row(X,Y)` an **own-block local-bijection row** if for every `Y` the
self-map `Phi_Y : X -> row(X,Y)` of the block-`X` full shift is a bijection
whose inverse is a cellular automaton with memory bounded uniformly in `Y`.
Linearity is not required.

The predecessor's **type (O)** is the special case `Phi_Y = L_Y(.) + beta(Y)`
with `L_Y` linear and bijective. The next definition supplies nonlinear
instances.

**Definition (graded-nilpotent own part).** Write `row(X,Y) = X + N_Y(X)`, where
`N_Y` is a local function reading `X` at a finite address set `S` and `Y`
arbitrarily. Suppose there is a finite chain of local functions
`X = P_0(X,Y), P_1, ..., P_D = 0` and a bound `D` such that `N_Y` maps the value
determined by `P_{k}` into the value determined by `P_{k+1}`; concretely, that
the formal substitution `N_Y^{(D)} = 0` after `D` iterations at each fixed `Y`.
Then

```text
Phi_Y^{-1} = sum_{k=0}^{D-1} (-N_Y)^{(k)}
```

is a finite composite of local functions, uniform in `Y`, so `Phi_Y` is an
own-block local-bijection row.

**Example (nonlinear, over F_2).** Two own-block factors with a nilpotent
address pattern. On `Z`, single track over `F_2`,

```text
row(x)(g) = x(g) + x(g+1) x(g+2),
```

read with the convention that the correction is applied from the largest
address inward, has `N` raising the minimal read address, so `N^{(3)} = 0` on
any window and `Phi^{-1} = I - N + N^{(2)}` is local. This is own-block
*nonlinear* and still peelable. (Contrast the central-`C_3` row of section 3,
which is not a local bijection.)

**Lemma 1.1 (peeling an own-block local-bijection row).** Let `F` be an
injective automaton on blocks `X, Y`, whose `X`-rows form an own-block
local-bijection row `Phi_Y`, and let `F' = ` the `Y`-rows of `F` evaluated at
`(X^*(Y), Y)`, where `X^*(Y) = Phi_Y^{-1}(0)` is the *correction*. Then `F'` is
injective, and:

* if `F'` is surjective, so is `F`;
* `F` is surjective iff `F'` is surjective.

*Proof.* Let `E(X,Y) = (Phi_Y(X), Y)`. `E` is a bijective cellular automaton:
it is injective because each `Phi_Y` is, its inverse `E^{-1}(Z,Y) =
(Phi_Y^{-1}(Z), Y)` is a cellular automaton by hypothesis (uniform local
inverse), and it fixes the second coordinate. Put `D = F o E^{-1}`. Then
`D(Z,Y) = (Z, T_Z(Y))` with `T_Z(Y)` the `Y`-rows of `F` at
`(Phi_Y^{-1}(Z), Y)`, and `T_0 = F'`. `F = D o E` with `E` bijective, so `F` is
injective iff `D` is, and surjective iff `D` is. `D` fixes `Z` and is injective,
so by (FIB) `F'` injective; if `F'` surjective then some fiber of `D` is
bijective... more directly, `D` is surjective iff some fiber is surjective
(FIB), and its `Z=0` fiber is `F'`. So `F` surjective iff `F'` surjective. QED

Lemma 1.1 is exactly Theorem 2.2 of the offset-corrected artifact with the
linear `L_Y` replaced by an arbitrary local bijection `Phi_Y`; the proof only
used that `E` is a bijective cellular automaton fixing the certificate.

**Peeling chain.** Say `F` is *peelable* under an ordering `X_1,...,X_r` if row
`a` of the successive corrected tails `F^{(1)} = F, F^{(2)}, ...` is, at each
step, one of: type (Z), type (O), or an own-block local-bijection row in `X_a`
whose data reads only later blocks. `F` is **fully peelable** if some ordering
peels every block, ending in the empty tail (no unknown left).

**Corollary 1.2.** An injective fully peelable automaton is surjective. This
extends `controlled-self-linear-feedback-ca-are-surjunctive`, which is the case
where every step is type (Z) or (O) and the last tail `L0_r` is a bijective
linear automaton. The empty tail is bijective (the identity on the empty product
of blocks), so the surjectivity conclusion follows by downward induction from
Lemma 1.1.

## 2. Corrected tails over a surjunctive subgroup

The predecessor artifacts leave surjunctivity "in the corrected tail" without
naming which tails are decidable. Here is the general class.

**Theorem 2.1 (surjunctive-memory tail).** Let `F` be injective and peel (via
type (Z), (O), and own-block local-bijection steps) to a corrected tail `F^{(k)}`
whose local rule reads only translations by elements of a subgroup `H <= G`. If
`H` is surjunctive, then `F` is surjective.

*Proof.* By Lemma 1.1 applied down the chain, `F^{(k)}` is injective and `F` is
surjective iff `F^{(k)}` is. `F^{(k)}` is a cellular automaton over `G` all of
whose memory lies in `H`. By (SUB) it is injective iff its `H`-copy is, and
surjective iff its `H`-copy is; the `H`-copy is injective, hence surjective
because `H` is surjunctive; so `F^{(k)}` is surjective, and therefore `F` is. QED

The tail's memory subgroup can be a **proper** subgroup of the original
automaton's memory group: peeling drops the rows of the peeled blocks, so any
generator read only by a peeled row disappears from the tail. This is what makes
Theorem 2.1 stronger than `surjunctive-guard-subgroups-force-surjectivity`,
which constrains the *original* automaton's coset structure.

**Concrete surjunctive tail classes.** `F` is surjective whenever it peels to a
corrected tail whose memory generates:

* the trivial group (the empty tail, Corollary 1.2, or a tail with no unknown);
* a residually finite, free, polycyclic, amenable, or (more generally) sofic
  subgroup (all surjunctive by Gromov--Weiss and `sofic-groups-are-surjunctive`);
* any subgroup already recorded surjunctive in the graph, e.g. via
  `leavitt-surjunctivity-tower` below its top.

Amenable tail memory also follows from `amenable-decoder-memory-forces-surjectivity`
through the Garden-of-Eden theorem; Theorem 2.1 subsumes it and every other
named surjunctive class at once.

## 3. Where strictness lives

**Theorem 3.1 (strictness needs a non-local-bijection own-block row).** Let `F`
be an injective three-factor automaton that is *strict* (not surjective). Then
in **every** ordering of any block presentation, the peeling chain halts before
the empty tail at a row whose own-block self-map `Phi_Y` is not a local
bijection.

*Proof.* If some ordering peeled every block by type (Z)/(O)/local-bijection
steps, then `F` would be fully peelable, hence surjective by Corollary 1.2,
contradicting strictness. So in every ordering some step is not one of those
three, i.e. its own-block row is not an own-block local-bijection row. QED

**The two minimal obstructions are direct-finiteness families.** A row that is
not an own-block local-bijection row fails in one of two ways.

* **(B1) Non-invertible own-linear part.** The row is own-linear but some `L_Y`
  is not bijective. Already for a single block with constant controllers this is
  `F = I + A` for an arbitrary linear cellular automaton `A`, and injectivity vs
  surjectivity is stable finiteness of `R[G]` (audit artifact, boundary B1).
* **(B3) Non-invertible own-block nonlinearity.** The own-block map is nonlinear
  and not a local bijection. The minimal case is the central three-cycle row:
  by `central-c3-quadratic-surjunctivity-iff-direct-finiteness`, injectivity vs
  surjectivity of `x + A(x R_t x)` on `Gamma x C_3` is exactly direct finiteness
  of `F_2[Gamma]`.

So the peeling boundary is sharp: everything a local bijection strips away, and
strictness sits precisely at own-block maps that are not local bijections, whose
smallest instances already encode the open direct-finiteness questions.

**Consequence for counterexample design (family N).** A strict three-factor
counterexample must contain, in every block presentation, a row whose own-block
self-map is not a local bijection. Any candidate whose every row is an
own-block local bijection under some ordering is surjective and can be discarded
at once. Combined with the nonsofic-forward-core filter and Theorem 2.1, a live
design must (i) present a non-surjunctive, hence nonsofic, memory group and (ii)
carry a genuinely non-invertible own-block row -- exactly the B1/B3 locus.

## 4. What this does not settle

Theorem 2.1 decides surjunctivity only relative to a surjunctive tail; it proves
no new group surjunctive. Theorem 3.1 localizes strictness but does not exclude
it: B1 and B3 are open. The three-factor claim, the recipient-affine claim, and
Gottschalk's conjecture remain open, and are equivalent group by group.
