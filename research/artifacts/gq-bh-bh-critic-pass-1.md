# BH swarm, critic pass 1

Lane `bh-critic`, 2026-09-18. Input: the subgraph map `gq-bh-bh-map-subgraph.md`
(f0965b866, read at origin/main 3903888ab) and the literature survey `gq-bh-bh-lit-survey.md`
(d7b638fef). Also read: the lane boards up to 08:45, the root `boone-higman-conjecture`,
and the nodes cited below. No claims of its own. Statuses are quoted from each node's
first status line.

## 1. Routes to `boone-higman-conjecture` and their sharpest gate

No route to the root has every requirement established. Each live route's gate, as one
question:

| Route | Sharpest open gate |
|---|---|
| Perfect shell (`boone-higman-via-perfect-shell-envelopes`) | For some infinite perfect f.p. decidable P, is there ν with E_ν f.p.? E_ν is simple for every ν. For one-ended P the germ gate needs the near-shift group R_ν = ⟨λ(P), s⟩ f.p. **and** a finite window with N ≥ 1 (`infinite-order-inputs-admit-mixed-near-relations`, 8af57b093). No one-ended P is known to pass. |
| Shell, general (fp-shell-envelopes / germ-stabilizers / enlarged / overgroups) | Same as the perfect shell route, without perfectness. `free-shift-shell-envelopes-are-not-finitely-presented` only kills the generic ν; mixed near relations always evade it. |
| Infinite shift compiler (Mallery–Zaremsky E_ν(P)) | Is E_ν(P) f.p. for some ν? Every other clause is free (Zaremsky 2405.18354, Prop. 5.3). |
| PBH (type (A)) | Does every decidable group embed in an f.p. type-(A) actor? Equivalently, in an f.p. simple highly transitive / MIF group. |
| Kazhdan BH / CK finite bi-index | Does the Chatterji–Kassabov envelope's simple core have finite bi-index? The general (T) ⇒ Max-n principle is dead (`kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`). The construction-specific case is open. |
| Simple inputs / simple FA inputs | Do infinite computably presented simple groups (or simple FA ones) embed in f.p. simple groups? |
| Local BH / isolated hosts | Local BH (a single inequation) plus Cornulier–Guyot–Pitsch Q4. |
| Towers (decidable-edge HNN) | Do HNNs over f.g. edges with decidable membership preserve f.p.-simple embeddability? |
| Fiber product | Find T f.p. with N ⊴ T f.g., T/N of type F_3, C_T(N) = 1, and finitely many T-classes in N. Clauses 5–6 pull against 3. |
| Lattice hosts (Bader–Shalom) | Do decidable simple groups embed in Bader–Shalom product lattices? |
| Ring / Leavitt hosts | f.p. central-simple hosts for decidable group algebras. The gq ring-gate bracket (48c3f0945) excludes every frame design, except its list (a)–(h). |

**Observation.** The shell routes and the infinite shift compiler have the same shape:
one enumeration ν, one explicit group, with only finite presentation open. So a
compression result for near relations would serve all of them at once. They should be
worked as one front, not separate lanes.

## 2. Overreach check (false greens and false reds)

### 2a. The biggest greens on main, and where they could fail

bh-lit flag F1 says the literature still lists as open several classes that main marks
ESTABLISHED:
- all f.g. linear groups in characteristic 0 and p;
- f.p. metabelian groups, BBMZ 5.3(7);
- spherical Artin groups, part of 5.3(13), which follow from linearity;
- B̃_n and C̃_n PBH.

If these hold, main contains solutions of printed problems. If they fail, many rows of
the map are false green by inheritance. Each has had at most one internal review.

The load-bearing steps to recheck end to end:

1. **`polynomial-linear-groups-satisfy-boone-higman`.** The host is
   G = R^n ⋊ E_n(R), with R = Z[1/m][t_1..t_k] and n ≥ max(k+4, 2N).
   - (a) **Finite presentation of the semidirect product.** Check f.p. of G itself, not
     only of E_n(R). R^n is not finitely generated as a group; it is cyclic only as an
     E_n(R)-module. Name the argument that gives G f.p., and confirm it is in
     `elementary-groups-over-polynomial-s-integers-are-fp` or its route.
   - (b) **Self-similarity.** G is claimed self-similar on Z_p^n × Z_p^k, with t acting
     by evaluation. A direct check: the sections substitute t ↦ e + p·t′, and constant
     terms divide by p inside Z[1/m] because p ∤ m. That looks right; confirm it is
     written in the node.
   - (c) **Zaremsky's hypotheses.** Check that Zaremsky 2405.09722 Thm 1.1 asks for
     nothing more than "f.p. self-similar": no self-replicating, level-transitivity or
     contracting condition. G is not contracting.
2. **`char-zero-linear-groups-embed-in-polynomial-s-integer-groups`.** Noether
   normalization over Z, miracle flatness and Quillen–Suslin over a PID. Miracle
   flatness needs a Cohen–Macaulay (e.g. regular) source. Check how the proof arranges
   that for an arbitrary f.g. domain of characteristic 0: by generic regularity after
   inverting an element, with that element then absorbed by a change of coordinates
   (the "Z[t][1/f] is finite free over Z[1/m][s]" step). This is the step most likely
   to hide a gap.
3. **`fp-metabelian-groups-satisfy-boone-higman` (BBMZ 5.3(7), marked reviewed).** Its
   characteristic-0 factor enters B_A through the same input that
   `char-zero-linear-groups-satisfy-permutational-boone-higman` marks unreviewed:
   `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, which bh-map lists
   as a lane proof. Check whether `review-metabelian-bh-2026-09-13.md` actually reviewed
   that node.
   - If it did, the unreviewed flag on the char-0 PBH node is stale and should be fixed.
   - If it did not, the metabelian PASS has an unreviewed dependency and its status line
     should say so.
   Either way the two nodes currently disagree.

These should go to an adversarial end-to-end check (bh-referee-c, plus gq-referee-a/b).
The 08:40 rule exempts claims that are load-bearing for BH itself, and these carry
several printed problems.

### 2b. Smaller items

- **bh-mcg board: "nV n ≥ 2 NOT excluded (RAAGs in 2V, Salo)".** This decides whether
  nV is a live host for closed MCGs. Cite the exact statement at source before any lane
  relies on it.
- **bh-outfn route `out-free-groups-virtually-embed-in-aut-free-groups`.** First check
  the literature on virtual splitting of 1 → F_n → Aut(F_n) → Out(F_n) → 1.
  - For MCGs, the Birman sequence is known not to virtually split (Chen–Salter-type
    results).
  - If the free-group analogue is known for n ≥ 3 (or for the relevant finite-index
    pullbacks), the route is dead and the abelianized-splitting node (518dae5bd) is a
    true but non-consequential step.
  - This is cheap to decide and prevents a long false hope.
- **Correctly scoped as written:**
  - `every-decidable-group-embeds-in-fp-self-similar-group` (refuted): kills only
    self-similar hosts.
  - `decidable-fp-groups-need-not-embed-in-rational-group`: kills only rational hosts.
  - `free-shift-shell-envelopes-are-not-finitely-presented`: kills only the generic ν.
  - `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`: kills only the general
    Max-n principle.
  - The root node states each scope correctly; no false red found.
- **Hyperbolic, Aut(F_n), BS(m,n), free-by-cyclic** are literature imports and fine.
  Punctured and bounded MCGs via Aut(F_n) are fine (Dehn–Nielsen–Baer with boundary).

## 3. Top five open questions (probability of a decisive answer × impact)

1. **End-to-end verification of the linear / metabelian chain** (§2a). High
   probability: it is a check, not a construction. High impact: it settles whether
   main already holds solutions of BBMZ 5.3(7) and the spherical part of 5.3(13), and
   whether many class rows are real. Owner: bh-referee-c, with gq-referee-a/b.
2. **One-relator groups, BBMZ 5.3(9).**
   `magnus-hnn-permanence-forces-one-relator-boone-higman` is an ESTABLISHED
   conditional theorem, so one permanence statement for HNNs over Magnus subgroups
   settles a survey item. Magnus subgroup membership is decidable (Magnus), so the
   decidable-edge gate is met. The missing piece is the f.p.-simple permanence itself.
   Owner: bh-one-relator, with bh-permanence.
3. **Out(F_n), BBMZ 5.3(3): decide the virtual-splitting question first** (§2b). A
   literature answer either kills the current route in an afternoon or confirms it is
   live. Owner: bh-outfn.
4. **Closure of BH under finite direct products.** Six attempts so far. PBH is closed,
   so the gap is exactly "BH without an (A)-action". A proof also revives the older
   metabelian route and product-of-trees cases. Owner: bh-permanence.
5. **Shell/compiler front on a minimal one-ended test input**, low probability but
   maximal impact. Use SL_3(Z) instead of St_N(R_L):
   - SL_3(Z) is perfect, f.p., decidable, one-ended and has (T).
   - It is already known to satisfy BH (linear), so a shell success is a pure
     calibration of the method.
   - A clean failure, e.g. no ν makes R_ν f.p. while meeting the window, is likely to
     generalize to every one-ended (T) input and would kill the shell routes for the
     inputs that matter (by `boone-higman-iff-simple-kazhdan-decidable-inputs`).
   Owner: bh-shell-universal or bh-shell-kazhdan.

## 4. Untested ideas (checked against ROSTER.md waves 1–4)

- **U1. SL_3(Z) as the calibration input for the shell germ gate** (item 5 above). No
  lane names it. gq-typeA-design uses St_N(R_L), which carries extra K_2 baggage
  irrelevant to the gate.
- **U2. One front for the shell routes and the Mallery–Zaremsky compiler** (§1). No
  lane owns `infinite-shift-higman-compiler` by name.
- **U3. Free Burnside groups, BBMZ 5.3(6).** No node on main, and no lane names it
  (bh-bbmz-problems should take it). First questions:
  - Does B(m,n), n odd and large, embed in an f.p. group with solvable WP and a type-(A)
    action?
  - Does the Ol'shanskii–Ivanov hyperbolic-limit structure give a shell enumeration
    with bounded near relations?
- **U4. BBMZ Question 4.7 (one-ended hyperbolic groups in V)** and **Question 5.6
  (every f.p. group in a type-F∞ group).** Named questions with no node and no lane.
  4.7 is exactly the kind of striking statement bh-cool is looking for.
- **U5. Cornulier–Guyot–Pitsch Question 4 (isolated groups).** A named conjunct of BH
  (`every-decidable-group-embeds-in-an-isolated-group`, OPEN), and possibly easier than
  BH itself. No lane names it.
- **U6. Named single groups with open nodes: Higman's group and Deligne's lattice.**
  - Higman's group is an amalgam of Baumslag–Solitar amalgams over free groups. Test it
    against the landed PBH amalgam closures (common-retract amalgams) and against
    bh-permanence's amalgam work.
  - Deligne's lattice is a non-residually-finite central extension of Sp_2g(Z). It is
    the natural test case for BH under central extensions, which no lane covers.
- **U7. Automatic groups (5.3(11)) and f.p. residually finite groups (5.3(12)).** No bh
  lane owns either. The f.p. RF case shares its Z_(l) and KMS machinery with the gq
  swarm (`kms-minsky-groups-contain-no-z-localized`, T_p parked).
