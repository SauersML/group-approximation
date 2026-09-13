# Idea lane nh-permanence-stress (2026-09-13)

Target: `non-hyperlinear-group`. Lens: try to prove that every group in a
large natural class is hyperlinear, and record the first construction step
where every known technique fails. Nothing here is established, and no node
was edited. Every citation is labelled with how it was checked.

## Known permanence (inputs)

Hyperlinearity passes to:
- subgroups, direct limits, direct products and free products
  (`hyperlinear-groups-closed-under-free-products`);
- extensions with amenable quotient;
- amalgams over amenable subgroups. This is stated in the introduction of
  arXiv:2311.09202, seen only through a search summary.

It is also closed under marked limits (`local-approximation-properties-are-marked-closed`).

Specific HNN nodes on main:
- `amenable-edge-hnn-preserves-hyperlinearity`;
- `ascending-hnn-cannot-create-nonhyperlinearity`.

Existence compressions on main:
- `hyperlinear-quotient-permanence-equivalence` (ESTABLISHED, formalized): universal hyperlinearity is equivalent to closure under arbitrary quotients.
- `nonhyperlinear-existence-is-two-generator-simple`.

## Approach 1: extensions with finite central kernel

**Idea.** Try to prove that if `1 -> Z/n -> E -> Gamma -> 1` is central and
Gamma is hyperlinear, then E is hyperlinear. Decomposing over the characters of
the centre gives `L(E) = ⊕_k L_{ω^k}(Γ)`, so E is hyperlinear exactly when
every twisted factor `L_{ω^k}(Γ)` is Connes embeddable. The known positive tools
all need something extra:
- Gamma amenable;
- E residually finite, which by `finite-central-extension-rf-iff-virtually-splits` means it virtually splits;
- E MF (Bachner–Dogon–Lubotzky Prop. 1.6, recorded and source-checked in
  `mf-hyperlinear-of-finite-normal-quotient`).

**What it would prove.** Permanence would kill every central-extension route
on main at once. A failure would be a non-hyperlinear group.

**Kill test (repo scan).** This is already the live crux on main:
- the Deligne-type covers and the Sp4 dichotomy;
- `agent-projective-kernel-arbitrary-phase-face-compiler`;
- the Dogon–Vigdorovich mechanism `hs-stability-forces-nonhyperlinear-central-extension`
  (ESTABLISHED by citation);
- `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` (ESTABLISHED).

**Where every technique stops.** Gamma is Kazhdan, residually finite and
hyperlinear, and ω has finite order with a non-virtually-split extension. None
of the three positive tools applies, and there is no Hilbert–Schmidt rounding
for Kazhdan almost-representations.

**Minimal question Q1.** For a residually finite hyperlinear Kazhdan group Γ
and ω ∈ H²(Γ; Z/2) whose extension does not virtually split, is `L_ω(Γ)`
Connes embeddable?

**Verdict.** Survives only as the map. It is the sharpest single-step
non-permanence locus found, but no new route; it duplicates the repo crux.

## Approach 2: quotients by the normal closure of one element

**Idea.** Prove `Γ/⟨⟨g⟩⟩` is hyperlinear whenever Γ is. Killing relators one at
a time reaches every finitely presented group, and marked closedness then
reaches every group. So one-element quotient permanence is equivalent to
universal hyperlinearity.

**Kill test.** It is a two-line corollary of `hyperlinear-quotient-permanence-equivalence`
together with `local-approximation-properties-are-marked-closed`.

**Verdict.** Killed as a duplicate. The only content left is the question of
which relators are safe. By approach 5, the first unsafe place known to every
technique is a quotient carrying property (T).

## Approach 3: HNN and amalgams over non-amenable associated subgroups

**Idea.** Prove hyperlinearity passes to the HNN extension of a hyperlinear A
over a finitely generated C ≤ A. Aanderaa's Britton-extension proof of
Higman's theorem builds every finitely generated recursively presented group
through layered HNN extensions (main: `boone-base-group-and-lemma-five`,
`aanderaa-rope-layers-are-mf-safe`; statuses not re-checked here). So
permanence over finitely generated associated subgroups would give every
finitely presented group, and then every group.

**Where it breaks.** Jung, arXiv:math/0506108 (abstract checked): for a
Connes-embeddable M, amenability is equivalent to all embeddings into R^ω being
unitarily conjugate. For non-amenable C, the two edge restrictions L(C) and
L(φ(C)) in a model of A need not be conjugate. Main's
`hnn-hyperlinearity-is-amalgamated-free-haar-unitary` shows the centralizer HNN
needs more than conjugacy: a Haar unitary in the relative commutant that is
free from the base with amalgamation.

**Kill tests (repo).** The relative-embeddability mechanism is already recorded:
- `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`;
- `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, conditional on stability.

**Calibration.** `arithmetic-pair-is-not-relatively-embeddable` (OPEN) asserts
that L(SL2(Z)) ⊂ L(SL2(Z[1/2])) is not relatively embeddable. SL2(Z[1/2]) is
linear, hence hyperlinear. So if that node holds, a non-relatively-embeddable
vertex inclusion cannot on its own force non-hyperlinearity: the obstruction has
to be global over the Bass–Serre tree. That makes local edge tests the wrong
place to look.

**Minimal question Q2.** Separate the two ingredients: (i) some model of A
makes the two edge restrictions unitarily conjugate; (ii) the conjugating
unitary can be made amalgamated-free. Does (i) imply (ii) in R^ω? If yes, the
HNN locus is exactly Jung's conjugacy problem for non-amenable edges. If no,
freeness is an independent obstruction, and it would be worth a node.

**Verdict.** Unclear. Mostly covered by main; Q2 is the only new sharpening.

## Approach 4: topological full groups

**Idea.** Prove that topological full groups of minimal topologically free
actions of hyperlinear groups on the Cantor set are hyperlinear.

**Positive inputs.** Ma, arXiv:2209.00580 (abstract checked):
- minimal topologically free residually finite actions have LEF topological full groups, hence sofic;
- for distal actions with dense free points, the full group is amenable iff the acting group is.
Also, every countable group embeds in Homeo(Cantor) through a Bernoulli
shift, so without minimality or freeness the class is everything.

**Where it breaks.** Ma's LEF argument uses residual finiteness of the action.
On the groupoid side, main has the binary Leavitt unit group, which is nonsofic
(`openai-leavitt-unit-nonsofic`, ESTABLISHED), while its hyperlinearity is
OPEN (`binary-leavitt-unit-group-hyperlinear`). So soficity permanence already
fails for non-residually-finite, non-free groupoid full groups, and
hyperlinearity is exactly the open frontier there.

**Minimal question Q3.** Is the derived topological full group of a minimal,
topologically free, NOT residually finite action of F_2 on the Cantor set
hyperlinear? And does it contain a nonsofic subgroup?

**Next test.**
1. Exhibit such an action (a non-residually-finite minimal free F_2-subshift).
2. Check whether its full group contains a V-type or Leavitt-type configuration group.

**Verdict.** Unclear. It gives a clean break line between residually finite
and non-residually-finite actions. The title grep of main found no node on
full-group hyperlinearity beyond the Leavitt nodes.

## Approach 5: hyperbolic groups with property (T)

**Idea.** Prove every hyperbolic group is hyperlinear.

**Known technique.** Cubulated implies virtually special, then linear, then
hyperlinear. Random groups at density below 1/6 are cubulated (Ollivier–Wise;
seen through a search summary only).

**Where it breaks.** Random quotients of hyperbolic groups at density above 1/3
have property (T) (Ashcroft, arXiv:2202.12318, abstract via ADS). (T) excludes
the cubulation route (Niblo–Reeves; not re-checked here), and no other
hyperlinearity technique for non-residually-finite hyperbolic groups is known
to me. Main's `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity`
(ESTABLISHED) turns flexible HS stability plus b₂ ≥ 1 into a non-hyperlinear
finite central extension.

**Minimal question Q4.** With overwhelming probability, is a random group at
density 1/3 < d < 1/2 hyperlinear? And do its finite central extensions
satisfy Q1?

**Verdict.** Survives as the map. Its central-extension twin is Q1.

## Synthesis: the first failing step

Every natural class tried fails at one of two mechanisms:

1. **Gluing across non-amenable pieces** (approaches 3 and 4). Jung's theorem
   says non-amenable subalgebras have non-conjugate embeddings, so
   amalgams, HNN extensions and groupoid full groups have no canonical way to
   match the vertex models.
2. **Twisting or killing over Kazhdan pieces** (approaches 1, 2 and 5). There
   is no normalized-HS rounding of Kazhdan almost-representations, so
   central twists and quotients with property (T) can't be certified.

The smallest single step where every known technique fails is Q1: a finite
central Z/2-extension of a residually finite hyperlinear Kazhdan group that
doesn't virtually split. That is already main's live crux. The new
sharpenings from this lane are Q2 (conjugacy vs amalgamated freeness for HNN
edges) and Q3 (non-residually-finite minimal free actions).

## Sources

- Jung, arXiv:math/0506108 (abstract).
- Ma, arXiv:2209.00580 (abstract).
- Ashcroft, arXiv:2202.12318 (ADS abstract).
- arXiv:2311.09202 (search summary, introduction).
- Gao–Junge, arXiv:2012.07940 (abstract; relative embeddability).
