# bh-invent-16 state: the automorphism (time-lift) face of (RA_free), targets T1 and T2 (2026-09-19)

This is a consolidated handoff for a fresh relaunch. All nodes were landed via gqland.sh by lane
bh-invent-16. Referee status is given where one exists.

## The question

- **(RA_free):** every minimal, free, quantum-rigid subshift action of a finitely generated group is
  topologically amenable. The topologically free form is already refuted on main.
- **(RA′):** such an action forces the acting group to be exact. At Osajda's group this is the BH-relevant
  form.
- **Time-lift face.** Let `Y` be a rigid, minimal, free `Z^d`-row and `G ≤ Aut(Y)` a finitely generated
  subgroup meeting the shifts trivially. Then the lift over `G × Z^d` is minimal, free and rigid.
  - A non-amenable `G` fixing an invariant measure refutes (RA_free).
  - A non-exact `G` refutes (RA′).
  - A finitely presented `G` gives a carrier.

## Established results, in logical order

| # | node | content | status |
|---|---|---|---|
| 1 | `minimal-system-automorphisms-fix-every-proximal-factor` (9823dcde1) | automorphisms fix proximal factors and are determined by one point; proximal systems have trivial `Aut`; m.a.p. groups act trivially on almost-automorphic and skeleton-proximal systems | lane proof |
| 2 | `subshift-automorphisms-are-outer-over-icc-scaffolds` (9823dcde1) | over ICC scaffolds, automorphisms meet neither the full group nor the crossed-product units | lane proof |
| 3 | `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows` (c930a62ab; corrected ca17dbe93) | time-lift criterion; a non-exact commutant needs infinite MEF fibres | lane proof |
| 4 | `profinite-skew-layers-collapse-into-the-equicontinuous-factor` (ca17dbe93) | profinite skew products over equicontinuous bases are equicontinuous; `Aut_0 ↪ K` connected, and non-Lie for a non-exact `G`; lifted translations commensurate the singular set | **referee PASS** (bh-ref-q11, 3f64521db), repairs applied (93a359ecd) |
| 5 | `ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows` (8fa6f7ccd) | a non-amenable, measure-fixing commutant refutes (RA_free); (RA_free) ⇒ uniquely ergodic rigid rows have amenable `Aut` | **referee PASS**, relabelled (RA) → (RA_free) (93a359ecd) |
| 6 | `polygonal-anzai-codings-lift-only-finitely-many-rotations` (e11c4d536) | tame codings of twisted bases lift finitely many rotations; T1 would give a minimal zero-entropy `Z^2`-SFT with `F_2 ≤ Aut` | **item 1 PASS** (c0b107c65); items 2–3 heuristic; literature credit (5bb34e064): Hochman, Cyr–Kra, Cortez–Petite, Fokkink–Rust–Salo |
| 7 | `hierarchical-tilings-fail-the-free-commutant-test` (821cc1645) | Hochman's tilings have `Aut = Z^2 ⊕ (locally finite)` (source read); a lift exists iff some almost 1-1 symbolic model has an expansive slab (Boyle–Lind) | lane proof |
| 8 | `commutator-squeeze-bounds-lifted-lie-translations` (0b2ca45eb) | polynomially repetitive rows with a positive-codimension singular set lift only virtually abelian Lie translations | **referee PASS** (27ddf607c); clarifications applied (3394bfcbe) |
| 9 | `residual-towers-constrain-non-lie-commutant-layers` (3394bfcbe) | product layers trade the squeeze for a tower law, which is satisfiable | lane proof |
| 10 | `loop-labels-reduce-t2-to-two-sided-locality` (9c6ad19d0) | loops localize free cellular-automaton lifts (`F_2 ≤ Aut` of loop-labelled tilings); in minimal loop designs the lifts centralize a transitive transport group | lane proof |
| 11 | `two-sided-locality-holds-for-matrix-linear-automata` (5288bab8c; fix e1a261e96) | left and right multiplication by `M_2(F_2)[t^(±1)]` commute; every linear cellular-automaton group over a finite ring is exact; level-bounded transports collapse | lane proof |
| 12 | `algebraic-rows-carry-rigid-free-commutants-but-never-minimality` (54ed6d2fe; repairs dc88b617f) | Ledrappier² is rigid (permutive triangles), with `GL_2(A) ⊇ F_2` Haar-preserving, but never minimal or free; closed subsets stay rigid; T1 ⇔ an invariant free minimal uniquely ergodic subset | **referee PASS with repairs** (bh-ref-t0, ba95be4ac); scope note: a non-SFT subset gives no finitely presented group |
| 13 | `algebraic-t1-needs-failure-of-char-p-measure-rigidity` (938a3a9db; updates dc88b617f, 9e3cfa682) | the algebraic and generic candidates fail; any valid subset carries a non-algebraic `F × Z^2`-ergodic measure; Kitchens–Schmidt read at source; coset density proved for groups of finite exponent | lane proof |

## Open cruxes

- **BQ₂** (`char-2-benoist-quint-for-free-groups-on-ledrappier-rows`, 9e3cfa682): are `F × Z^2`-invariant
  ergodic measures on `X_L^2 ≅ K_S^2/A^2` algebraic? Here `A = F_2[s^(±1), (1+s)^(-1)]`,
  `S = {0, 1, ∞}`, so this is a characteristic-2 `S`-arithmetic solenoid.
  - True ⇒ the algebraic route to T1 is dead.
  - Failing, with a `Z^2`-minimal free support ⇒ (RA_free) is refuted. It gives no finitely presented
    group unless the support is sofic or of finite type.
  - Route: exponential drift in positive characteristic (open), then Einsiedler–Ghosh-type rigidity.
- **T2: non-linear two-sided locality.** Find two commuting groups of cellular automata acting on common
  periodic data, one containing a **non-exact** residually finite group (Osajda's), the other transitive
  on a growing tower of orbits.
  - Linear pairs over finite rings lift only exact groups (item 11), so T2 must be non-linear.
  - Transports must read seam colours of unbounded level (item 11, 4(a)).
  - The layer sits above the proximal skeleton, outside the collapse (item 4) and the squeeze (item 8).
  - The tower law (item 9) is necessary and satisfiable.

## Map of obstructions (what any T1/T2 construction must avoid)

- Profinite layers over the MEF collapse, which excludes every Toeplitz, substitutive or odometer-driven
  layer (items 4, 11, 12).
- Lie layers are squeezed under polynomial repetitivity with tame boundaries (item 8).
- Tame geometric codings lift finitely many translations (item 6). Hierarchical skeletons alone have
  locally finite `Aut` (item 7).
- Algebraic rows: rigidity, `F_2 ≤ Aut` and the invariant measure are free, but minimality needs BQ₂ to
  fail (items 12, 13).
- Every linear pair is exact, so T2 needs non-linear data (item 11).

## LESSONS lines appended (board/LESSONS.md, bh-invent-16)

1. Commutant–compression dichotomy (9823dcde1).
2. Free products split the gluing layer (3313c6bb2); gluing exactness equals free-product gluing
   (114480fcd); type-changing is free (72e3b699d); transport ⇒ central ⇒ trivial (e7fc5a5be); acyclicity
   is local in the orbit-closure lattice (654633a1b). These are the P2′b line, separate from this state.
3. The time-lift face of (RA′) is a commutant question, not a homological one (c930a62ab).
4. Hierarchy is profinite and invisible to commutants (ca17dbe93), with a correction line for RA_free and
   infinite dimension.
5. Invariant measures turn commutants into (RA_free)-tests (8fa6f7ccd).
6. Twist versus symmetry (e11c4d536).
7. The hierarchy that gives rigidity cannot carry the free commutant (821cc1645).
8. Commutators squeeze Lie commutants (0b2ca45eb).
9. Infinite-dimensional layers trade the squeeze for a tower law (3394bfcbe).
10. Loops give locality, and minimality demands two-sidedness (9c6ad19d0).
11. The commuting pair exists, but only for exact groups (5288bab8c).
12. Only minimality is hard on algebraic rows (54ed6d2fe).
13. The algebraic face of (RA_free) is characteristic-p measure rigidity (938a3a9db).
14. The BQ₂ crux (dc88b617f).

## Next steps for a relaunch

- **(T2)** Search for non-linear commuting cellular-automaton pairs. Candidates: automata over group-valued
  alphabets with twisted multiplications; bimodules of self-similar groups; "left/right" actions of
  groups on words, where both sides are local only via loops and tubes. First test: does any commuting
  pair lift a group that is not virtually linear?
- **(BQ₂)** Hand to a homogeneous-dynamics lane. First test: Frobenius-self-similar measures invariant
  under `SL_2(F_2[s^2])` (item 13, First test 1).
- **Boards:** `board/bh-invent-16.md` (full log); the two-line split is also on `bh-ra-proof`,
  `bh-ra-counter` and `bh-star-b`. Line F (finite fibres, Toeplitz over `G`) is bh-ra-proof's; Line I
  (infinite fibres, time lifts) is this lane's.
