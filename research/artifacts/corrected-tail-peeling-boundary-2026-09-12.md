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
self-map `Phi_Y : X -> row(X,Y)` of the block-`X` full shift is a bijection.
Linearity is not required, and nothing more is needed:
`E(X,Y) = (Phi_Y(X), Y)` is then a bijective cellular automaton on a full shift
over a finite alphabet, so by Curtis--Hedlund--Lyndon its inverse
`(Z,Y) -> (Phi_Y^{-1}(Z), Y)` is a cellular automaton, and the inverses are
local uniformly in `Y`.

The predecessor's **type (O)** is the special case `Phi_Y = L_Y(.) + beta(Y)`
with `L_Y` linear and bijective.

**Instances (corrected 2026-09-12; the first version's graded-nilpotent example
was false, see Section 5).**

* *Track shears.* If block `X` has tracks `(u,v)`, every composite of the shears
  `(u,v) -> (u + f(v,Y), v)` and `(u,v) -> (u, v + h(u,Y))`, with arbitrary
  local `f` and `h`, is an own-block local bijection; the inverses are the
  opposite shears. These rows are nonlinear in the block, but they also peel
  track by track with type-(O) steps. For
  `Phi(u,v) = (u + f(v,Y), v + h(u + f(v,Y), Y))`, peel `u` with correction
  `u* = -f(v,Y)`; the tail row in `v` is the pure shear `v + h(0,Y)`.
* *A single-track nonlinear bijection.* Let `t` have order three and, over `F_2`,
  put `row(x)(h) = x(h) + x(h)x(ht) + x(ht)x(ht^2)`. The rule acts separately on
  each left coset `g<t>`, as the map
  `(a,b,c) -> (a + ab + bc, b + bc + ca, c + ca + ab)` on `F_2^3`. That map fixes
  `000, 100, 010, 001, 111` and cycles `110 -> 011 -> 101 -> 110`, so the row is a
  bijection. It is nonlinear and lives on one track, so it cannot be split into
  tracks: this is where Lemma 1.1 reaches beyond type (O). It is the same-track
  control of the audit artifact's boundary B3; the B3 family `x + A(x R_t x)`
  with an arbitrary linear `A` is in general not a bijection.

**Lemma 1.1 (peeling an own-block local-bijection row).** Let `F` be an
injective automaton on blocks `X, Y`, whose `X`-rows form an own-block
local-bijection row `Phi_Y`, and let `F' = ` the `Y`-rows of `F` evaluated at
`(X^*(Y), Y)`, where `X^*(Y) = Phi_Y^{-1}(0)` is the *correction*. Then `F'` is
injective, and:

* if `F'` is surjective, so is `F`;
* `F` is surjective iff `F'` is surjective.

*Proof.* Let `E(X,Y) = (Phi_Y(X), Y)`. `E` is a bijective cellular automaton
fixing the second coordinate, and `E^{-1}(Z,Y) = (Phi_Y^{-1}(Z), Y)` is a
cellular automaton, as above. Put `D = F o E^{-1}`. Then `D(Z,Y) = (Z, T_Z(Y))`
with `T_Z(Y)` the `Y`-rows of `F` at `(Phi_Y^{-1}(Z), Y)`, and `T_0 = F'`.
`F = D o E` with `E` bijective, so `F` is injective iff `D` is, and surjective
iff `D` is. `D` is injective and fixes `Z`, so its fiber `F' = T_0` is
injective. If `D` is surjective, every fiber is. Conversely, by (FIB) one
surjective fiber makes `D` surjective. So `D` is surjective iff `F'` is, and
hence `F` is surjective iff `F'` is. QED

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

## 5. Verification notes (gk-vf-positive, 2026-09-12)

Lemma 1.1, Corollary 1.2, Theorem 2.1 and Theorem 3.1 pass. Section 7 of
`research/artifacts/gk-vf-positive-verification-2026-09-12.md` has the details.

* **The "Example (nonlinear, over F_2)" in Section 1 is false.**
  * `row(x)(g) = x(g) + x(g+1)x(g+2)` sends both constant configurations to `0`, so it is not
    injective.
  * `N(x)(g) = x(g+1)x(g+2)` is not nilpotent under composition: `N(N(x))(g) = x(g+2)x(g+3)x(g+4)`.
* **The graded-nilpotent inverse formula also fails for nonlinear `N`.** `(I+N)(x - N(x))` equals
  `x - N(x) + N(x - N(x))`, which is not `x` in general.
* **Replacement instances.** Nonlinear own-block local bijections exist: composites of track shears
  `(u,v) -> (u + f(v,Y), v)` and `(u,v) -> (u, v + h(u,Y))` with arbitrary local `f` and `h`.
* **Resolved by the author (gk-p-tails, 2026-09-12).** The false example and the graded-nilpotent
  definition have been removed from Section 1. Section 1 now lists the track shears (which also
  peel track by track with type-(O) steps) and the single-track order-three control
  `x(h) + x(h)x(ht) + x(ht)x(ht^2)`, which permutes `F_2^3` on each left coset of `<t>`. It also
  drops the local-inverse hypothesis, which is automatic by Curtis--Hedlund--Lyndon.
