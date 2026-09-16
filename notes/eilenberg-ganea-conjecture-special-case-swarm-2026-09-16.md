# Eilenberg--Ganea conjecture: special-case lane (swarm, 2026-09-16)

Agent: `hi-spec-eilenberg-ganea-conjecture`. Angle: special case / strengthening.
Target root: `eilenberg-ganea-conjecture`. This lane locked nothing: every node it
touches is new. Nothing was committed.

## 1. Angle

The graph attacks EG from the counterexample side through Bestvina--Brady kernels
(`acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`,
`bb-kernel-gd-two-if-l-lies-in-contractible-2-complex`,
`epsilon-map-conjecture-gives-poincare-kernel-gd-three`). This lane works on the positive
side instead. It asks which natural torsion-free classes of cohomological dimension 2
provably have geometric dimension 2.

The class chosen is the one singled out by the 2023--2026 literature: *virtually
free-by-cyclic* groups. By `virtually-rfrs-cd2-coherence-characterization` (Fisher--Linton--
Sánchez-Peralta), a finitely generated virtually RFRS group of cd at most 2 is virtually
free-by-cyclic iff `b_2^(2) = 0`, iff it is coherent. So EG for torsion-free virtually
free-by-cyclic groups would give EG for every coherent finitely generated virtually RFRS group
of cd 2.

The difficulty is the finite extension. A free-by-cyclic group has a 2-dimensional
`K(π,1)` (the mapping torus of a graph map). Whether a torsion-free finite extension of a
group of geometric dimension 2 again has geometric dimension 2 is itself a case of EG, and
the obvious constructions (coinduction, Borel construction, orbit of fibrations) raise the
dimension.

## 2. State of the art (sources, dated)

**Status.** EG is open as of 2026-09-16. No source checked this session claims a proof or a
counterexample for torsion-free groups.
- The graph's `eilenberg-ganea-or-whitehead-is-false` (Bestvina--Brady 1997, Theorem 8.7) is
  the only unconditional link to Whitehead.
- The graph's counterexample-side routes are conditional on the ε-map conjecture.

**Freshness checks this session.**
- *arXiv API, `all:"Eilenberg-Ganea"`, newest first, fetched 2026-09-16.*
  - arXiv:2401.15667: analog LS category, off-topic.
  - arXiv:2107.10643: Bowditch taut spectrum, many cd 2 / gd 3 phenomena for families.
  - arXiv:1912.01692: equivariant dimensions with operators.
  - arXiv:1911.03457: EG problem for families via trees.
  - arXiv:1207.1474: Coxeter groups, virtually cyclic stabilisers.

  None proves torsion-free EG for a new class, and none treats finite extensions.
- *arXiv API, `all:"virtually free-by-cyclic"`, fetched 2026-09-16.*
  - 2607.07496, 2603.26580, 2603.16763 (FLSP), 2511.21293, 2505.18054, 2504.14192,
    2403.18758 (Fisher), 2302.11500 (Kielak--Linton), 2003.06354.
  - The abstracts do not mention geometric dimension, EG, or whether torsion-free virtually
    free-by-cyclic groups have 2-dimensional classifying spaces. This is abstract level only;
    bodies were not grepped.
- *Kielak--Linton, arXiv:2302.11500* (v1 2023-02-22, v3 2024-06-27, "to appear in GAFA").
  Abstract fetched: a homological characterisation of virtually free-by-cyclic groups among
  hyperbolic virtually compact special groups. One-relator groups with torsion are virtually
  free-by-cyclic.
- *Fisher, arXiv:2403.18758* (v2). From the listing summary: RFRS groups with vanishing
  second L²-Betti number are virtually free-by-cyclic.
- *Fisher--Linton--Sánchez-Peralta, arXiv:2603.16763v1* (2026-03-17). Pinned on main in
  `virtually-rfrs-cd2-coherence-citation` (checked there 2026-08-31). For finitely generated
  virtually RFRS `G` with `cd_k ≤ 2`: coherent iff `b_2^(2) = 0` iff virtually free-by-cyclic,
  with the kernel possibly infinitely generated.

**Classical positive cases** (recalled, unverified pins, not re-fetched):
- one-relator torsion-free groups: Lyndon asphericity of the presentation complex;
- soluble groups of cd 2: Gildenhuys 1979, where the non-finitely-generated ones are
  subgroups of `Q`;
- graphs of free groups;
- 3-manifold groups with nonempty boundary: 2-dimensional spines;
- right-angled Artin groups over flag complexes of dimension at most 1: the Salvetti complex;
- the graph's `bb-kernel-gd-two-if-l-lies-in-contractible-2-complex`.

**Relevant boundary.** Brady--Leary--Nucinkis 2001 (recalled) show that the proper-action
analogue fails for groups with torsion. So any finite-extension argument must use
torsion-freeness.

**Graph state before this lane.** There was no claim about geometric dimension of virtually
free-by-cyclic or graph-of-free-groups classes: grep for "graph of free groups",
"geometric dimension" and "Scott-Wall" over `research/`, and `bin/cairn search --similar`, on
2026-09-16.

## 3. What was proven

The full proofs are in `research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md`.

1. **`free-by-virtually-cyclic-torsion-free-groups-have-gd-two`** (ESTABLISHED by the direct
   route `free-by-virtually-cyclic-gd-two-proof`).
   - *Statement.* Let `G` be torsion-free and `N ⊲ G` free, of any rank. Suppose `G/N` acts on
     a tree without inversions and with finite vertex stabilizers. Then `gd G = cd G ≤ 2`.
   - The hypothesis holds when `G/N` is virtually cyclic, by Lemma L: an explicit transfer
     construction of an action on the line `(1/2)Z`.
   - *Proof.* Stabilizers are torsion-free finite extensions of `N`, hence free (Serre,
     Stallings--Swan). Bass--Serre gives a graph of free groups, and the Scott--Wall graph of
     spaces is 2-dimensional.
2. **`virtually-free-by-cyclic-normal-fibre-gives-gd-two`** (ESTABLISHED by
   `virtually-free-by-cyclic-normal-fibre-gd-two-proof`, requiring 1). Let `G` be
   torsion-free. EG holds for `G` in either case:
   - **(i) Normal fibre.** Some finite-index `H` has a surjection to `Z` with free kernel
     normal in `G`. This covers `b_1(H) = 1`, `G`-conjugates of the fibration equal to `±`
     itself, and invariant fibrations with free kernel, in which case `G` is free-by-cyclic.
   - **(ii) Periodic monodromy.** `G` is virtually `F_n × Z` with `n ≥ 2`. Here the normal free
     subgroup is the center of the normal core, and the quotient is finitely generated
     virtually free (Karrass--Pietrowski--Solitar).
3. **`torsion-free-virtually-free-by-cyclic-groups-have-gd-two`** (new OPEN hole, with
   Attempts).
   - The residual case is the one where every fibration with free kernel has a `G`-conjugate
     that is not `±` itself, and the monodromy is not periodic.
   - Via FLSP, the hole would give EG for coherent finitely generated virtually RFRS
     torsion-free groups of cd 2.

**What is new, honestly assessed.**
- *Items 1 and 2.* No statement of either was found (abstract-level arXiv checks, graph
  search). The proofs are short combinations of standard tools. Item 1 in particular is
  plausibly folklore to experts in Bass--Serre theory. The genuinely lane-specific content is:
  - identifying the finite-extension step as *the* EG question for the FLSP class;
  - the precise dividing line: normal fibre / centre available vs orbit rank at least 2;
  - the two mechanisms, normal fibre and centre, that settle the periodic and rank-1 cases.
- *Item 3.* A reduction/hole, not a theorem.
- *Nothing here decides EG or affects the counterexample side.*

## 4. Approaches tried and where each dies

**A. Virtually free-by-cyclic, general case.** See artifact §4.
1. **Orbit intersection.** `N = ⋂ ker(ψ∘c_g)` is free and normal, but `G/N` is virtually
   `Z^r` with `r ≥ 2`. The graph-of-spaces construction over `R^r` gives `gd ≤ r + 1`.
2. **Averaging fibred classes.** It needs a `Q`-invariant, convex fibred component, and `Q` may
   permute components with none fixed. Convexity of components was recalled from Kielak's
   Newton-polytope description of BNS for free-by-cyclic groups (Invent. Math. 2020,
   unverified). It is only needed for the unverified remark in B2.
3. **Coinduction** to `X^{G/H}`. Free, but of dimension `2[G:H]`. No equivariant
   2-dimensional retract.
4. **L²/Kaplansky criterion.** For `cd G ≤ 2` and a finite presentation complex `K`, `π_2 K`
   is a finitely generated projective with von Neumann dimension `χ(K) − χ^(2)(G)`.
   - Here `χ^(2)(G) = 0` (Lück's mapping torus theorem for `H`, divided by the index).
   - So a finite 2-dimensional `K(G,1)` exists iff `G` has a deficiency-1 presentation.
   - Presentations of finite extensions have very negative deficiency, with no Tietze control.
5. **A tree action for `G`.** None is visible when `b_1(G) = 0` and the fibre is not normal.
   No example of such a torsion-free `G` was constructed either. Constructing one, or proving
   it cannot exist, is a concrete next step.

**B. Other special cases considered and dropped** (earlier in this session).
1. *Torsion-free virtually `F_m × F_n`.*
   - Either factor-preserving or swapping, coinduced actions on products of trees give a free
     action on `T × T`.
   - Standard-looking and already a product-of-trees lattice situation, so not recorded.
     Theorem A does not obviously cover it: when factors are swapped, neither factor is normal
     in `G`.
2. *Leary groups `G_L(S)` and Bestvina--Brady kernels for aspherical acyclic `L`.*
   - `G_L(∅)` acts freely on a contractible 2-dimensional level set, so `gd ≤ 2` is immediate,
     but it is not a new class relative to Leary arXiv:1512.06609.
   - Kernels `H_L` for non-contractible aspherical `L` meet the same Morse-sweep obstruction
     as `bb-kernel-gd-two-if-l-lies-in-contractible-2-complex`: attaching maps are not
     cofibrations after the first level.
3. *Amalgams over gd-2 edge groups.* Scott--Wall gives dimension `max(2, 1 + 2) = 3`. Dies.
4. *Countable-to-finitely-generated reduction.* Mapping telescopes add a dimension. No gain.
5. *One-3-cell variant.* Absorbed by the Whitehead-lane notes. Not pursued.

## 5. Next steps

1. **Settle the residual case on an example.** Find a torsion-free `G ⊇ F_n ⋊_φ Z` (`φ`
   atoroidal, say) with `b_1(G) = 0`. Or prove that such `G` always admits a normal fibre or a
   free-by-(virtually free) structure. Such an example is the test case for the hole.
2. **Hyperbolic `H`.** Here `G` is torsion-free hyperbolic and virtually compact special
   (Hagen--Wise for `H`, recalled). Look for a 2-dimensional CAT(0) or `C'(1/6)` model, or
   use Kielak--Linton's homological characterisation on `G` itself.
3. **Deficiency.** For `G` with `χ(G) = 0`, try to prove deficiency 1 using the Wall
   obstruction being zero (`G` is of type F) and Kaplansky. Stably-free-to-free for
   `ZG`-modules of virtually free-by-cyclic groups is the algebraic crux.
4. **Graph edges.** A route `torsion-free-virtually-free-by-cyclic-groups-have-gd-two` plus
   `virtually-rfrs-cd2-coherence-characterization` ⇒ "EG for coherent f.g. virtually RFRS
   torsion-free cd 2 groups" can be added as a node pair once someone wants that target named.
   The implication itself is one line.

## 6. Files

- `research/free-by-virtually-cyclic-torsion-free-groups-have-gd-two.md` (claim)
- `research/free-by-virtually-cyclic-gd-two-proof.md` (route, `requires: []`)
- `research/virtually-free-by-cyclic-normal-fibre-gives-gd-two.md` (claim)
- `research/virtually-free-by-cyclic-normal-fibre-gd-two-proof.md` (route)
- `research/torsion-free-virtually-free-by-cyclic-groups-have-gd-two.md` (hole)
- `research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md` (proofs)

check.sh on these six paths: exit 0 (2026-09-16). It gave an advisory that the lane top is not
reachable from a root. That is correct: a special case does not imply the root.
