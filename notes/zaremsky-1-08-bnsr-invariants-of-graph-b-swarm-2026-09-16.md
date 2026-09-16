# zaremsky-1-08-bnsr-invariants-of-graph-braid-groups: swarm pass, 2026-09-16

Agent: `swarm-zaremsky-1-08-bnsr-invariants-`.

**Target.** `zaremsky-1-08-bnsr-invariants-of-graph-braid-groups`, Zaremsky
Problem 1.8: "Compute the BNSR-invariants of graph braid groups." It is open,
and its only answer route is `zaremsky-1-08-by-formula`.

**Hole worked.** `graph-braid-characters-are-hyperplane-affine`, locked this
pass. It is a leaf of the single explicit-formula route,
`graph-braid-sigma-formula-via-matching-criterion`.

**Outcome: solved negatively.** The claim is false, and the counterexample
holds for every subdivision of `K_4`, so no reading of "sufficiently
subdivided" rescues it. The positive problem (Problem 1.8) is still open.

## 1. Orientation

**Read.**
- The root and `zaremsky-1-08-by-formula`.
- `graph-braid-group-sigma-invariants-explicit-formula` and its Attempts.
- `graph-braid-sigma-formula-via-matching-criterion`.
- `graph-braid-ascending-matching-complexes-give-sigma` (+ proof),
  `graph-braid-ascending-matching-complex-criterion-is-exact`,
  `graph-braid-matching-complex-connectivity-explicit`.
- `graph-braid-nonzero-euler-characteristic-sigma-asymmetric` (+ proof).
- Artifacts `research/artifacts/zp-graph-braid-sigma-2026-09-13-part{1,2,3}.md`.

**The hole.** Part 2, §1, Lemma 2 classifies hyperplane classes of
`X = UD_nΓ` as pairs `(e, κ)`. There `κ` distributes the parked particles
over the components of `Γ_e = Γ − ē`. A function on oriented classes is an
*affine cocycle*. The hole asserts that for sufficiently subdivided `Γ` every
class in `H^1(X; ℝ) = Hom(B_nΓ, ℝ)` is affine.

Its Attempts proposed two plans:
- compare dimensions with Ko–Park;
- pull back along a Haglund–Wise / Crisp–Wiest map into a RAAG, and ask
  whether restriction is onto. The Attempts already flagged this step as
  risky.

**Duplicate search.** `bin/cairn search` for "hyperplane-affine",
"non-affine character" and "graph braid character" found no node proving or
refuting the claim.

## 2. Literature gate (checked 2026-09-16)

**arXiv API queries**, sorted by submission date:
- `all:"graph braid groups"`: 35 hits; the newest is 2609.06589, from
  2026-09-06.
- `all:"graph braid" AND abs:invariant`.
- `all:"BNSR" AND all:braid`.
- `abs:"Bieri Neumann Strebel" AND abs:braid`.
- `abs:"Sigma-invariants" AND abs:"cube complex"`.
- `abs:"graph braid" AND abs:"character"`.

Two further queries (`all:"graph braid" AND all:"Sigma"` and
`abs:"Bieri-Neumann-Strebel" AND abs:graph`) returned malformed or empty
responses and give no evidence either way.

**No paper found computes BNS or BNSR invariants of graph braid groups, or
asks whether their characters are hyperplane-affine.** The relevant hits:
- **Ko–Park**, *Characteristics of graph braid groups*, arXiv:1101.2648
  (2011). I read the e-print TeX source. The `H_1` theorem is labelled
  `thm:H1Bn`, and is Theorem 3.16 by counting the section-3 theorem
  environments: `H_1(B_nΓ) = ℤ^{N_1+N_2+N_3+β_1} ⊕ ℤ_2^{N'_3}`. Used only for
  interpretation (artifact §7), not in the proof.
- **Zaremsky**, *Separation in the BNSR-invariants of the pure braid groups*,
  arXiv:1507.08597 (2015). About pure braid groups only.
- **de Miranda e Pereiro–Sgobbi**, *The BNS invariants of the braid groups
  and pure braid groups of some surfaces*, arXiv:2308.12377 (2023). About
  surface braid groups.
- **An–Oh–Park**, *Hierarchical geometry and right-angled Artin groups in
  graph braid groups*, arXiv:2609.06589 (2026-09-06). Abstract read: an HHG
  structure on `UD_nΓ`, RAAG subgroups, maximal rank of free abelian
  subgroups. Nothing on characters or Σ.
- **An–Oh**, *On the large-scale geometry of graph braid groups via cubical
  structures*, arXiv:2602.15636 (v3, 2026). Abstract read: quasi-isometry
  classification and 2-strand product subcomplexes. Nothing on Σ.
- Other 2024–2026 titles seen, none about Σ:
  - Jain–Vo, arXiv:2603.07807;
  - An–Drummond-Cole–Knudsen corrigendum, arXiv:2602.20228;
  - Hainaut–Knudsen–Wawrykow, arXiv:2510.00201;
  - Jankiewicz–Schreve, arXiv:2404.08863;
  - Appiah–Dani–Ge–Hudson, arXiv:2403.08623;
  - Berlyne, *Graph of groups decompositions of graph braid groups*,
    arXiv:2209.03860 (2022, title only).
- **Zaremsky's open-problem list.** The scratchpad copy is dated July 12,
  2026; item 8 is unchanged, so Problem 1.8 is still posed there.
- **Unverified.** A pass before a context reset also recorded
  arXiv:math/9310202 and a Madrid seminar page listing a talk on Σ-invariants
  of Artin groups (Nov 2024). I did not re-fetch either this session.
- **Openness of `Σ^1`** is attributed to Bieri–Neumann–Strebel (1987). It is
  standard, but I did not re-check the theorem number.

## 3. Result

**Claim `two-strand-k4-and-theta-braid-characters-not-affine`**, proved by
route `two-strand-k4-and-theta-braid-characters-not-affine-proof`
(`requires: []`). The full proof is in
`research/artifacts/graph-braid-hyperplane-affine-counterexample-2026-09-16.md`,
§§1–6.

**Statement.** Let `Γ` be any subdivision of `K_4` (including `K_4`), or any
subdivision of `Θ_3` with every arc at least 2 edges long. Then affine
cocycles on `UD_2Γ` span a subspace of `H^1(UD_2Γ; ℝ)` of dimension at most
`β_1(Γ)` (3, resp. 2), while `b_1(UD_2Γ) ≥ 4` (resp. `≥ 3`).

**Proof in four lines.**
1. If `Γ_e` is connected, all X-edges over `e` lie in one class. Adjacent
   `z, z'` in `Γ_e` give the square `{e, [z,z']}`, and configuration graphs of
   connected graphs are connected. So an affine cocycle is `a∘τ` for some
   `a ∈ C^1(Γ)`, where `τ({e}∪R) = e`.
2. `τ` is a chain map in degrees ≤ 1 that kills square boundaries. So affine
   classes lie in the image of the dual of `τ_*: H_1(X) → H_1(Γ)`, of
   dimension ≤ `β_1(Γ)`.
3. Euler characteristic:
   `e(UD_2Γ) = C(N,2) − M(N−2) + C(M,2) − Σ_v C(deg v, 2)`. This is `−3` for
   every subdivision of `K_4` and `−2` for every subdivision of `Θ_3`. Since
   `dim X = 2`, `b_1 ≥ 1 − e`.
4. For these graphs every `Γ_e` is connected (case check, artifact §6).

Everything is elementary and self-contained; Ko–Park is not used.

**Refutation recorded.** The hole now carries
`refuted_by: [two-strand-k4-and-theta-braid-characters-not-affine]`, plus an
Attempts bullet. The dry-run `check.sh` (exit 0) reports:
- established: `two-strand-k4-and-theta-braid-characters-not-affine`;
- refuted: `graph-braid-characters-are-hyperplane-affine`;
- invalidated: route `graph-braid-sigma-formula-via-matching-criterion`.

**Hypothesis check.** For `n = 2`, the improved subdivision hypothesis
(Kim–Ko–Park arXiv:0805.0082, Prue–Scrimshaw; Abrams' original condition
asks for more) needs:
- each path between essential vertices of length ≥ 1;
- each essential cycle of length ≥ 3.

`K_4` itself and `Θ(2,2,2)` both satisfy it. In any case
`H^1(X; ℝ) = Hom(π_1X, ℝ)` for connected `X`, so non-surjectivity onto
`H^1(UD_2Γ)` needs no hypothesis.

## 4. Where the earlier plans die

**RAAG restriction.** Haglund–Wise send a special cube complex to the
Salvetti complex of its hyperplane crossing graph, taking each edge to the
generator loop of its hyperplane. A generator's dual cochain therefore pulls
back to a hyperplane-constant cochain. So restriction `H^1(RAAG) → H^1(B_nΓ)`
has image exactly the affine classes, and it is not onto for `K_4` or
`Θ_3`. This is the step the old Attempts flagged.

**Cube-affine heights see only affine characters.** An equivariant height
that is affine on cubes descends to an affine cocycle (artifact §7).
Theorem M of part 2 is correct but covers only the affine subspace.

**Cubical subdivision** does not enlarge the affine image, since
`c(H) = c'(H−) + c'(H+)` (artifact §7).

**Graph subdivision** does not help for `K_4`: every subdivision fails at
`n = 2`. For `Θ_3` it can even hurt:
- `Θ(1,2,2)` and `Θ(1,3,3)` have all characters affine. An arc of length 1
  disconnects `Γ_{[p,q]}`, which creates extra classes.
- `Θ(2,2,2)` and every further subdivision fail.

So the affine image is not subdivision-invariant. Under the existential
reading `Θ_3` would survive, but `K_4` refutes both readings.

## 5. What the refutation does and does not do to Σ

These points are in the artifact's last remark, "What this means for Σ".

**The counterexample groups are free.**
- In `UD_2K_4` each X-edge lies in exactly one of the 3 squares, and the
  squares meet only at vertices, so `B_2K_4 ≅ F_4`.
- In `UD_2Θ(2,2,2)` every square has a free edge, so `B_2Θ_3 ≅ F_3`.
- `run_probe.sh` confirms that these complexes collapse to graphs.

So `Σ^m = ∅` for these groups, and the missing characters are harmless
there.

**Non-affine characters also occur in non-free groups (evidence).** Take
`K_4` with a triangle glued at a vertex, and `K_4` with a triangle on a
bridge, both at `n = 2`, `k = 2`:
- both have `b_1 = 8` and affine image 7;
- `b_2 = 1` and `3` respectively;
- both contain two disjoint cycles, so `ℤ^2 ⊆ B_2Γ`.

**Openness gives a structural dichotomy.** `Σ^1` is open, `Σ^m ⊆ Σ^1`, and
the affine subspace `A` is proper for such `Γ`, so `S(A)` has empty interior.
Hence:
1. The open claim `graph-braid-ascending-matching-complex-criterion-is-exact`
   (Σ-members have affine representatives with good ascending complexes)
   implies `Σ^m(B_nΓ) = ∅` whenever non-affine characters exist.
2. If Theorem M certifies any class for such a `Γ`, the exactness claim is
   false.

**Probe of the dichotomy.** `sigma1_probe.py` tests point 2 at `m = 1`,
`n = 2`, over all sign patterns on hyperplane classes. Output is in
`sigma1-probe-2026-09-16.txt`.
- Calibration: the cycle and the triod (`B_2 = ℤ`) have 2 passing patterns
  each; all free cases of rank ≥ 2 have none.
- The three non-free graphs (dumbbell and the two `K_4`-plus-triangle graphs)
  have none.

So no contradiction was found. This is consistent with `Σ^1 = ∅` there, but
proves nothing.

**The refuted claim was logically redundant.** The exactness claim, as
stated, already says every Σ-member is affine. So an explicit criterion
could be:

> `[χ] ∈ Σ^m` iff `χ ∈ A`, and some admissible representative satisfies the
> matching-complex condition.

This would need only `give-sigma`, `exact` and `connectivity-explicit`. A
future route to `graph-braid-group-sigma-invariants-explicit-formula` could
drop the affine claim. It would still have to fix the horizontal
(non-generic) representative gap that the old route glossed over:
Theorem M needs `c ≠ 0` on every class. I did not write this route: it
targets a different claim, and the gap is real.

## 6. Evidence and a conjecture (not nodes)

**Scripts.** In `experiments/graph-braid-hyperplane-affine-2026-09-16/`:
- `hyperplane_affine.py`, exact over `ℚ` with `EXACT=1`;
- `run_all.sh`, 30 cases, output `results-2026-09-16.txt`;
- `sigma1_probe.py` with `run_probe.sh`, 15 cases, output
  `sigma1-probe-2026-09-16.txt`.

All runs are single-threaded, capped by `timeout 600`, and the whole set
finishes in seconds.

| `Γ` | `n` | `b_1` | affine image |
|---|---|---|---|
| `K_4`, k = 1, 2, 3, (1,2,1,3,1,2) | 2 | 4 | 3 |
| `Θ_3`, k = 2, 3, 4, (2,2,3) | 2 | 3 | 2 |
| `Θ_3`, (1,2,2), (1,3,3) | 2 | 3 | 3 |
| `Θ_4`, k = 2 | 2 | 6 | 3 |
| `K_5`, k = 1 | 2 | 6 | 6 |
| `K_{3,3}`, k = 1 | 2 | 4 | 4 |
| cycle, figure-eight, dumbbell, triangle with legs, lollipop | 2 | 1, 4, 4, 4, 2 | same |
| triod, `K_{1,4}`, H-tree | 2 | 1, 3, 2 | same |
| `K_4` + triangle at a vertex / on a bridge, k = 2 | 2 | 8, 8 | 7, 7 |
| `Θ_3`, k = 3 | 3 | 3 | 2 |
| `K_4`, k = 2 | 3 | 4 | 3 |
| cycle, lollipop, triod, `K_{1,4}`, H-tree | 3 | 1, 3, 3, 11, 6 | same |

The first 28 rows match Ko–Park's `b_1`. I did not check the two
`K_4`-plus-triangle rows against Ko–Park's `N_1` term.

**Conjecture.** Suppose every topological edge is cut into at least 2 edges,
and the subdivision hypothesis holds for `n`. Then:
- the affine image has dimension `β_1(Γ) + N_1(n, Γ)`;
- the deficit is `N_2(Γ) + N_3(Γ)`, the 2-cut exchange classes plus the
  planar triconnected classes;
- all real characters are affine iff `N_2 = N_3 = 0`.

**Trees: sketch only, not proved.** Every tree row above is affine. The idea
of a proof is to analyse, at each essential vertex, functions of how parked
particles are distributed among branches, and to compare with the local
Farley–Sabalka / Ko–Park count. I have not written this carefully, so there
is no node.

**General `n`.** Lemmas 1–3 of the artifact hold for every `n ≥ 2`, as long
as `|V(Γ_e)| ≥ n − 1`. With Ko–Park's `b_1 = β_1 + 1` for `K_4` and `Θ_3`,
the failure persists for all `n` under the subdivision hypothesis. That
remark depends on Ko–Park and is not a node.

## 7. Next steps

1. **Route repair.** Write the replacement route above once the horizontal
   case of Theorem M is handled. Options: a Bux–Gonzalez horizontal version,
   or perturbing `c` within its sign cell without changing `χ_c`.
2. **Test the dichotomy for larger `n`.** Extend `sigma1_probe.py` to `n = 3`
   on graphs with non-affine characters and non-free braid groups, e.g. `K_4`
   or `Θ_3` with a pendant cycle. Any passing pattern there refutes
   `graph-braid-ascending-matching-complex-criterion-is-exact`, via openness.
3. **If no pattern ever passes,** try to prove the candidate hole "`B_nΓ` has
   a non-affine character ⟹ `Σ^1(B_nΓ) = ∅`". Berlyne's graph-of-groups
   decompositions (arXiv:2209.03860, title only) look like the natural tool.

## Referee (2026-09-16)

**Checked.**
- Read every file of this pass, the refuted hole, the invalidated route, the
  root, the exactness claim and artifact part 2 (whose §1 Lemma 2 defines the
  hyperplane classes `(e, κ)`; with `n = 2` and `Γ_e` connected there is one
  class per edge, matching the artifact's §1 definition by opposite edges of
  squares).
- Re-derived the proof line by line: Lemma 1 (configuration graphs of trees
  are connected), Lemma 2 (one class per edge when `Γ_e` is connected),
  Lemma 3 (`τ({e}∪P) = e` is a chain map in degrees ≤ 1 killing square
  boundaries, so affine classes lie in the image of `τ_*^∨`, dimension
  `≤ β_1(Γ)`), the Euler count (`−3` for every `K_4` subdivision, `−2` for
  every `Θ_3` subdivision; redone by hand), `b_1 ≥ 1 − e` for a 2-complex,
  and the `Γ_e` connectivity case checks (including the arc-length-1 failure
  for `Θ_3`). No gap found; the quantifier "sufficiently subdivided" is
  handled because every subdivision of `K_4` fails.
- Independent code (different construction: cochain matrices, rank of
  `[δ_0 | affine basis]` minus rank `δ_0`, modulo two large primes) for
  `K_4` with arcs 1, 2 and (1,1,1,1,1,4), and `Θ_3` with arcs 2, (2,3,4),
  (1,2,2), (1,4,2): `b_1 = 4, 3`, affine image `3, 2`, and full image 3 when
  an arc has length 1. Agrees with the solver's exact runs.
- Replayed `run_all.sh` and `run_probe.sh` in a scratch copy: outputs are
  byte-identical to the committed result files (under 10 s total).
- Ko–Park arXiv:1101.2648: fetched the e-print source; `thm:H1Bn` states
  `H_1(B_nΓ) = ℤ^{N_1+N_2+N_3+β_1} ⊕ ℤ_2^{N'_3}`, and counting the shared
  theorem counter in §3 gives Theorem 3.16, as claimed. An–Oh–Park
  arXiv:2609.06589 exists (submitted 2026-09-06), abstract has nothing on Σ.
  arXiv API queries `abs:"graph braid" AND (abs:BNS OR abs:BNSR OR
  abs:"Sigma-invariant" OR abs:Bieri)` and `abs:"graph braid" AND
  abs:hyperplane` returned no entries (2026-09-16).
- Duplicates: `bin/cairn search --similar` finds only the refuted hole
  itself. Claim id is 51 characters.

**Changed.**
- Claim `two-strand-k4-and-theta-braid-characters-not-affine`: reworded the
  last paragraph so the proved statement (about `H^1(UD_2Γ; ℝ)`) is separated
  from the identification with `Hom(B_2Γ, ℝ)`, which uses the subdivision
  theorem exactly as the refuted claim's own statement does.
- Artifact §7: replaced "By Abrams' theorem" with the subdivision-invariance
  argument and the correct attribution of the improved hypothesis.
- This note, §3: the `n = 2` hypothesis quoted is the Kim–Ko–Park /
  Prue–Scrimshaw improvement, not Abrams' original condition.

**Not re-checked.** The Bieri–Neumann–Strebel theorem number for openness
of `Σ^1` (the solver already marks it); the Σ remarks in artifact §7 are
evidence and nothing established depends on them.

**Verdict.** Sound. The direct proof is complete and self-contained; the
refutation of `graph-braid-characters-are-hyperplane-affine` and the
resulting invalidation of `graph-braid-sigma-formula-via-matching-criterion`
are correct. Landed with small wording fixes.
