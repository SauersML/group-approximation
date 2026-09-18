# The adversarial side of (★′) (lane bh-star-b, 2026-09-18)

**Task.** Find what could make (★′) impossible: a minimal, topologically free, quantum-rigid SFT, with
torsion-free isotropy, over `Λ_1 × Λ_1` or over any finitely presented `Λ_0 ⊇ G`. Calibrate every
candidate obstruction against the two positive cases, `∂T_m ⊠ ∂T_n` over `F_m × F_n` and the Ã₂
boundary skew shifts.

**Status.** Lane work, not reviewed. The landed nodes carry their own status lines.
- `quantum-rigid-subshifts-cluster-the-modifications-of-each-point` (ESTABLISHED);
- `v-stabilized-stabilizer-engines-are-never-finitely-presented` (ESTABLISHED; rests on the unreviewed
  necessity theorem);
- `quantum-rigid-minimal-topfree-subshift-actions-are-amenable` (OPEN).

## 0. Verdict

- **No kill of (★′).** Nothing found makes (★′) impossible over every candidate `Λ`. Both positive
  cases pass every test below.
- **One new structural theorem, which kills a design family.** Quantum rigidity clusters the
  modifications of each point and forces its isotropy to carry them along.
  - So a point with infinite isotropy and a homoclinic partner (an *emitter*) rules out rigidity at
    every scale, in every coding, with no finite-type or minimality hypothesis.
  - Coinduction from a subgroup with infinitely many double cosets is never rigid.
- **One route closed.** The Cuntz-stabilized stabilizer engines are never finitely presented, for every
  infinite finitely generated vertex group. The same holds for `B * Z` compactified by its vertices.
  - This is the "input at an infinite emitter" alternative of SYNTHESIS v5, in every form that goes
    through quantum rigidity.
- **One decisive open question.** Is every such rigid action topologically amenable? If so, (★′) fails
  over every non-exact group, and the master route cannot reach Osajda's decidable non-exact input.

## 1. Candidates examined

| # | Candidate obstruction | Outcome | Calibration |
|---|---|---|---|
| 1 | Finite modifications in minimal SFTs (known) | kills every minimal SFT with a homoclinic pair | both positive cases have none |
| 2 | Far modifications in non-SFT subshifts | the far-modification lemma holds for every subshift; its SFT hypothesis was only used for `z ∈ X`, and local legality at scale `D` is enough | none needed |
| 3 | **Isotropy scattering** (new) | kills every point whose isotropy moves some modification support arbitrarily far; homoclinic partners at infinite isotropy are the main case | ends pass: modifications share tails (`∂T`), or share sectors (Ã₂) |
| 4 | **Coinduction / independent cosets** (new) | never rigid when `Λ\Λ'/Λ` is infinite | the escape is exactly the Cornulier finite-double-coset regime, still open |
| 5 | Single free branch (known) | needs a multi-ended factor | `Λ_1` one-ended gives nothing; over `Λ_0 * Z` it holds with `Λ_0` trivial and is consistent with ends |
| 6 | Entropy (topological or sofic) | first order, subsumed by walls (rows 1–3); over non-amenable `Λ` there is no entropy formula to invoke | — |
| 7 | Invariant measures | open; implied by row 8 | both positive cases are boundary actions with no invariant measure |
| 8 | **Topological amenability (RA)** | open, and decisive for non-exact inputs | every proved rigid example is amenable |
| 9 | Torsion-free isotropy (K′) | compatible with end-type isotropy, which is cyclic or abelian in the examples | no tension found |
| 10 | Product structure `Λ_1 × Λ_1` | rigidity is product-stable, so factors suffice; no product-specific obstruction | — |

## 2. The clustering principle (row 3), stated for designers

For a `D`-rigid subshift `X` and any `x ∈ X`:
- every two modifications of `x` have supports within `2D` of each other;
- every `h ∈ Stab(x)` moves each support `Δ` to within `2D` of itself.

**What it allows.**
- Trivial isotropy: the input acts freely and scales.
- End-type isotropy: `Stab(x)` translates toward `x` along a coarse ray contained in every
  modification support.

**What it forbids.**
- Emitters, with homoclinic neighbours permuted by the isotropy.
- Any construction in which two far regions can be modified independently: coinduction, independent
  coset data, independent branches.

**Miniature over `Z`.**
- `{at most one 1}`, the one-point compactification, has isotropy `Z` at `0^Z` and homoclinic partners
  `δ_n`. It is killed. Its `V`-less full group is Houghton's `H_2`, which is not finitely presented.
- `{nondecreasing}`, the two-point compactification, has the same isotropy. It is rigid at every scale:
  monotone chain, direct check in the node.

These are exactly the two members `Z⁺` and `Z ⊔ {±∞}` of the blow-up family in
`stabilizer-engines-embed-in-every-branch-compactification`.

## 3. Consequences for the gates of SYNTHESIS v5

- **Gate 1 (IE).** "A hard input sits at an infinite emitter" is incompatible with every rigid design.
  - That covers the ring route and the group route, and the stabilizer engines once `× G_V` is
    applied.
  - What remains of gate 1 is **only** the `V`-less question: is `D(F_S)` finitely presented, Reid's
    group being the case `S = Z`?
  - Any proof must use something that `× G_V` destroys, such as the homology `H_*(S)` carried by the
    engine groupoid. A Brown or Stein–Farley argument that works equally for the Cuntz-stabilized
    groupoid is excluded.
  - The Houghton model (`H_2`) points toward "not finitely presented" for `S = Z`. That is suggestive
    only.
- **Track A′ over `Λ_1 * Z`.** The symmetric emitter coding, with the tree compactified by the
  vertices, is never rigid. Designs must break the symmetry with fibre data so that the input acts
  freely, as the minimal free subshift of `free-products-with-z-inherit-m2-from-decidable-free-subshifts`
  does.
- **Blow-ups (bh-invent-13).** Replacing the emitter by an `S`-compactification `K` moves the test to
  the remainder points of `K`.
  - For a hard input `S`, `K` must have infinite remainder, with end-type remainder points: in effect
    a compression boundary of `S`.
  - That is the geometry v5 says hard inputs lack. Heuristic; not proved.
- **(RA).** This is the adversarial question for (★′) itself.
  - Every rigidity mechanism on main produces amenable dynamics: compression toward ends, fp boundary
    hosts read backwards, and `Z^2` determinism.
  - So does every transfer: products, deterministic extensions and subsystems.
  - Rows 3–4 kill the constructions that would leave amenability.
  - The routes that (RA) cannot touch are those that keep the input out of the acting group of a rigid
    subshift: the `V`-less engines and Track B.

## 4. Suggested work for other lanes

- **bh-free-56 / bh-free-60 (Reid's group).** Test your Stein–Farley argument against the
  Cuntz-stabilized engine. If the argument also applies there, it contradicts
  `v-stabilized-stabilizer-engines-are-never-finitely-presented`, so it must break somewhere.
  - Watch the vertex-point links. The Houghton-type germ structure at `B`-vertices (`H_2` for `B = Z`)
    is the expected failure point.
- **bh-g2-buildings.** Test (RA) with Mozes-type SFTs over products of trees.
  - Is any of them measure-preserving?
  - If one is, is it quantum rigid? The clustering principle is a quick necessary test.
- **bh-synth-lead.**
  - Gate 1 should be split: the (IE)-rigid form is dead, and the `V`-less engines stay open.
  - (RA) should be added as the analytic gate for (★′).
- **bh-invent-13.** The engine of `K` needs end-type remainder points. For an FW input `S`, check
  whether the relevant difference sets are commensurated, hence finite or cofinite. That would kill
  blow-ups for Kazhdan inputs outright.

## 5. Sources

Everything above is derived from nodes on main: the definitions of (Q1)–(Q3), the wall certificate,
the necessity theorem, and the dynamics of the engine. Standard facts are recalled, not re-read:
- Houghton's `H_2` is not finitely presented (Brown 1987);
- exactness is equivalent to having a topologically amenable action on a compactum;
- boundary actions of hyperbolic groups and of Euclidean-building lattices are amenable;
- an amenable action with an invariant probability measure forces the group to be amenable.

No literature search was run for the clustering principle. Its content is an elementary extension of
the far-modification lemma already on main.
