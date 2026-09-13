# Idea lane bh-contracting-selfsim: self-similar hosts for Boone--Higman

Target: `boone-higman-conjecture`. Lens: self-similar groups and their Cantor
hosts (Zaremsky, arXiv:2405.09722, Theorem 1.1). Date: 2026-09-13.

Status: ideas only. Nothing here is a theorem or changes any node's status.

## What this lens already has in the graph (read first, not repeated)

- `boone-higman-via-universal-fp-self-similar-host` is **dead**: subgroups of
  self-similar groups are residually finite
  (`self-similar-hosts-contain-only-residually-finite-groups`).
- `every-fp-rf-group-embeds-in-fp-self-similar-group` is refuted. Condition (N1),
  bounded composition factors, is realized by
  `cycle-transposition-lef-group-has-no-regular-tree-action`.
- `boone-higman-via-rover-nekrashevych-hosts` is **dead**. Kazhdan subgroups of
  `V_d(H)` are residually finite, and Deligne's lattice is excluded.
- `fw-subgroups-of-eventually-similar-groups-virtually-embed` extends the Kazhdan
  obstruction to eventually similar groups over shifts of finite type, with FW
  subgroups landing virtually in products of vertex groups.
- `baumslag-gersten-embeds-in-no-rover-nekrashevych-group`: every almost
  automorphism of a regular rooted forest sends `a` to 1. Its stated scope
  excludes Brin--Thompson `nV`, twisted `SV_G`, rational similarity groups and
  hosts with non-isometric local groupoids.
- `el3-z-t-embeds-in-no-host-with-number-field-local-groups`: `SL_3(Z[t])`
  embeds in no eventually similar host whose vertex groups are linear over
  `Qbar`.
- `decidable-fp-groups-need-not-embed-in-rational-group`: finite-state
  (rational) hosts are not universal.

Every one-dimensional, tree-automorphism-local host class is therefore already
obstructed. The approaches below stay inside the lens but leave that class.

---

## 1. Self-similar Brin--Thompson hosts `nV_d(H)`

**Idea.** Let `H <= Aut(T_d)` be finitely presented and self-similar. Let
`nV_d(H)` be the group of homeomorphisms of `(X^omega)^n` that cut the cube into
finitely many bricks `C_(u_1) x ... x C_(u_n)`, map bricks to bricks by prefix
replacement in each coordinate, and apply an element of `H` in each coordinate
section. For trivial `H` this is Brin's `nV`. Any universal Cantor host must avoid
all the one-dimensional obstructions above, and `nV_d(H)` is the smallest
self-similar class the graph has not excluded. The hope is that
`[nV_d(H), nV_d(H)]` is finitely presented and simple for finitely presented
`H`, and that non-residually-finite Kazhdan inputs such as Deligne's lattice, or
the Baumslag--Gersten group, embed in it.

**What it would prove.** A host class outside every existing obstruction. Its
universal form, every decidable `G` embedding in some `nV_d(H)`, would give
Boone--Higman, provided finite presentation holds.

**Kill tests run now.**
- *Does the FW obstruction transfer?* Hand check of the mechanism behind
  `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`.
  - In one dimension, `g` maps every cone of depth `>= D_g` to a cone, and only
    finitely many cones are shallower. So `g` commensurates the set of cones.
  - In dimension 2, the bricks `C_u x C_v` with `|u| >= D_g` but `|v| < D_g`
    form an infinite set on which `g` need not act by brick similarities.
    Commensuration of the brick set is not visible, and the argument does not
    transfer as written. **Not killed.**
- *Literature on nV geometry.*
  - Kato, arXiv:1504.06680, abstract: "We prove that nV has Serre's property FA,
    for every n."
  - Callard--Salo, arXiv:2208.00685, abstract: "the higher-dimensional
    Brin-Thompson groups mV admit distortion elements; in particular, 2V
    (unlike V) does not admit a proper action on a CAT(0) cube complex."
  - So the two tools that constrain subgroups of `V` do not carry over to `2V`:
    Farley's proper cubical action, and undistorted cyclic subgroups (the basis
    of the Baumslag--Solitar exclusion quoted in
    `almost-automorphism-conjugate-to-proper-power-is-equicontinuous`).
  - No source found stating the Haagerup property or property (T) for `2V`
    either way. A search-engine summary claimed Brothier--Jones call it open;
    arXiv:1805.02177v1 contains no occurrence of "2V", so that claim is
    unverified and not used.
- *Finite presentation of `nV_d(H)` for finitely presented `H`.* No source
  found. That is the first thing a deep lane must settle, e.g. through a
  Stein--Farley complex argument like the one behind finite presentation of
  `V_d(H)`.

**Next kill test (cheap).** Does `BS(1,2)` embed in `2V`, or in `2V_3(H)` with
the ternary odometer/doubling `H` from `baumslag-gersten-odometer-fixed-point-proof`?
If an element of `2V` conjugate to its own square must be equicontinuous, the
Baumslag--Gersten obstruction transfers and this approach loses its main selling
point.

**Verdict: survives** (not tested at its core).

---

## 2. Growing alphabets (spherically homogeneous trees)

**Idea.** Condition (N1) kills fixed-degree trees for inputs with unboundedly
large composition factors. Replace `T_d` by the spherically homogeneous tree with
level degrees `d_1, d_2, ...` tending to infinity. Define self-similarity along
shifted degree sequences, and look for a Thompson--Nekrashevych-type group over
it.

**What it would prove.** Hosts for residually finite decidable inputs such as the
cycle-transposition group, which no regular tree carries.

**Kill test run now (hand argument).**
- A Thompson-type group needs prefix replacements between cones at different
  depths, so it needs isomorphisms between the subtrees below them.
- The subtree below depth `k` has degree sequence `(d_(k+1), d_(k+2), ...)`.
  Two cones at depths `k != l` are isomorphic only if these tails agree, so if
  the sequence is not eventually periodic, every almost automorphism preserves
  cone depth up to finitely many exceptions.
- The resulting group is a union of level-preserving iterated wreath products.
  It contains nothing like `V` and no finitely presented simple subgroup of the
  intended kind.
- If instead the sequence is eventually periodic with period `p`, grouping `p`
  levels gives a regular tree of degree `d_(k+1)...d_(k+p)`, and (N1) returns
  with that bound.

**Verdict: killed** (sketch, by the depth-type argument above). Growing degrees
either destroy cross-depth similarity or collapse back to a regular tree.

---

## 3. Self-replicating Cantor hosts (the vertex group is the host)

**Idea.** The FW obstruction only pushes Kazhdan inputs into products of
**vertex groups**. So look for an eventually similar group `E` over a shift of
finite type whose vertex groups are, up to isomorphism, `E` itself. Concretely,
`E` would be finitely generated by finitely many prefix replacements whose
sections are words in the generators of `E` acting on the cone. This is a fixed
point of the Nekrashevych-group construction `H |-> V_d(H)`, with germs taken
in the host rather than in a tree automorphism group.

**What it would prove.** A host class in which the FW, number-field and
equicontinuity obstructions do not apply. Local maps are non-isometric, so this
is in the "not covered" list of
`baumslag-gersten-embeds-in-no-rover-nekrashevych-group`.

**Kill tests run now.**
- *FW reduction.* Hand check: with vertex groups equal to `E`, the conclusion of
  `fw-subgroups-of-eventually-similar-groups-virtually-embed` becomes "`K_0`
  embeds in `E^n`", which is circular. **Not an obstruction.**
- *Equicontinuity (Baumslag--Gersten).* The proof uses tree-automorphism local
  maps. Here local maps are non-isometric, and the node's stated scope excludes
  them. **Not an obstruction.**
- *Complexity* (`complexity-bounded-host-classes-are-not-universal`, cited in
  `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`). A single fixed
  `E` has one word-problem time bound, so no single self-replicating host is
  universal. A family of them is not excluded.
- *Well-definedness.* A "finitely many prefix replacements whose sections lie in
  `E`" definition is recursive. Existence as a group of homeomorphisms needs a
  contraction or finite-depth condition, and without one the sections may never
  resolve. No source or construction found. **Unclear.**

**Verdict: unclear.** Speculative; the kill tests only show that the current
obstructions do not reach it.

---

## 4. A single benchmark input against every self-similar host class

**Idea.** Take the free product
`G* = BG * Lambda * K * SL_3(Z[t])`:
- `BG`: the Baumslag--Gersten group;
- `Lambda`: Deligne's lattice, the decidable non-residually-finite Kazhdan group
  of `deligne-lattice-embeds-in-no-rover-nekrashevych-group`;
- `K`: the finitely presented residually finite decidable group of
  `decidable-fp-groups-need-not-embed-in-rational-group`.

**What it would prove.** Nothing new mathematically. It is one decidable test
input that any proposed universal host class must contain, and that is excluded
at once from:
- every self-similar group, because `Lambda` is not residually finite;
- every `V_(d,r)(H)`, by `BG` and by `Lambda`;
- every eventually similar group over a shift of finite type with residually
  finite or `Qbar`-linear vertex groups, by `Lambda` and `SL_3(Z[t])`;
- every rational group, by `K`.

Any new host proposal (approaches 1 and 3, twisted Brin--Thompson `SV_G`, full
Cantor groups) can be tested first on whether it could contain `G*`.

**Kill tests run now.**
- A free product of finitely generated groups with solvable word problem has
  solvable word problem (normal forms).
- Each obstruction quoted is a non-embedding statement, so it passes to
  overgroups: if `G*` embedded, the factor would too.
- One gap: the decidability of `Lambda` is taken from the Deligne node, not
  re-read here.

**Verdict: survives** (as a benchmark, not a route).

---

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Self-similar Brin--Thompson hosts `nV_d(H)` | survives: FW and undistortedness arguments do not transfer; finite presentation of the host unknown |
| 2 | Growing alphabets | killed: no cross-depth similarity, or back to a regular tree |
| 3 | Self-replicating Cantor hosts | unclear: no current obstruction applies; existence not constructed |
| 4 | Benchmark input `G*` | survives, as a test input |

Sources checked in this lane: arXiv:1504.06680 (abstract), arXiv:2208.00685
(abstract), arXiv:1805.02177v1 (text, for the absence of any 2V statement), and
the repository nodes named above at origin/main 991380d00.
