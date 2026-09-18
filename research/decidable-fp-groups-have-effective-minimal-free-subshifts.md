---
rg: 2
id: decidable-fp-groups-have-effective-minimal-free-subshifts
kind: claim
title: Every infinite finitely presented group with solvable word problem carries a nonempty effectively closed minimal free subshift
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that asks for a minimal free subshift OF FINITE TYPE on some finitely presented overgroup; this asks only for an EFFECTIVELY CLOSED minimal free subshift on the group itself, with no finite-type condition.
  gjs-countable-groups-have-free-minimal-subflows: that gives a free minimal subflow of 2^G for every countable group by a non-effective construction; this asks that one such subflow be effectively closed, which Zorn or an arbitrary minimal subsystem does not provide.
  f2-groups-have-paradoxical-free-minimal-subshifts: that adds a paradox for groups with free subgroups and is not effective; this asks for effectiveness for all infinite finitely presented groups with solvable word problem.
  rf-toeplitz-subshift-has-computable-language: that is a computable minimal topologically free Toeplitz subshift over effectively residually finite groups; this needs freeness at every point and makes no residual finiteness assumption.
---

**OPEN.** Premise (M2) of route
`minimal-free-sft-via-plane-constant-minimal-simulation`.

**Statement.** Let `Λ_0` be an infinite finitely presented group with solvable
word problem. Then there are a finite alphabet `B` and a nonempty subshift
`Y ⊆ B^{Λ_0}` such that:
- `Y` is effectively closed: some recursively enumerable set of finite patterns
  defines `Y` as the set of configurations avoiding all of them;
- `Λ_0` acts minimally on `Y`;
- `Λ_0` acts freely on `Y`: `λ·y = y` for some `y ∈ Y` forces `λ = 1`.

The action is `(λ·y)(μ) = y(μλ)`.

**Equivalent forms, by hand.**
- A minimal effectively closed subshift over a finitely generated group with
  solvable word problem has decidable language.
  - *Non-occurrence is r.e.:* compactness.
  - *Occurrence is r.e.:* by minimality a pattern that occurs meets every point
    within a bounded radius, and compactness makes this a finite search. This
    is the argument of `plane-constant-minimal-sft-factors-are-effective-minimal-proof`,
    step 4, with `Φ` the identity.
- So (M2) is equivalent to the existence of a computable point `y` whose
  orbit closure is free and minimal, with a computable uniform recurrence
  function.
  - *Forward:* decidable language gives a computable point by extending
    patterns, and the recurrence radius is found by search.
  - *Backward:* a pattern on a ball `B(n)` occurs in the orbit closure iff it
    occurs in `y` within radius `f(n)`.

**Why it is a separate prerequisite.**
- *Necessary for the plane-constant design class.* By
  `plane-constant-minimal-sft-factors-are-effective-minimal`, any minimal SFT
  over `Λ_0 x Z^2` whose `Λ_0`-freeness is witnessed by a `Z^2`-invariant free
  `Λ_0`-factor produces an instance of (M2) for `Λ_0`.
- *Necessary for (P1) in weakened form.* A nonempty minimal free SFT over a
  finitely presented group `Λ` is an instance of (M2) for `Λ` itself. Jeandel
  (context only) gives solvable word problem, and every SFT is effectively
  closed. So (P1) implies that every decidable input embeds in an infinite
  finitely presented group satisfying (M2).
- *It can fail independently of (M1).* (M1) is a simulation statement that
  takes (M2)'s output as input and says nothing about existence.

**Known instances (hand arguments, not imported).**
- *`Λ_0 = Z^d`.* Take `d` Sturmian subshifts with computable irrational slopes,
  one on each coordinate of the product. The product under `Z^d` is minimal,
  because orbits of the product group are products of orbits. It is free,
  because stabilizers are products of stabilizers and an infinite minimal
  `Z`-subshift is free. It has decidable language, because Sturmian languages
  with computable slope are decidable.
- *Products.* If `G_1` and `G_2` satisfy (M2), so does `G_1 x G_2`, by the
  product subshift with the same argument.
- *Groups already carrying a minimal free SFT.* The SFT itself, which gives
  Labbé's shift over `Z^2` again (`minimal-aperiodic-wang-shift-exists`).
- *Not known here:* any infinite simple Kazhdan group, or the Clapham envelope
  of one. These are the inputs the Boone--Higman route needs
  (`boone-higman-iff-simple-kazhdan-decidable-inputs`).

## Attempts

**Attempt 1 (2026-09-17): minimal subsystem of an effective strongly aperiodic
subshift.** Aubrun--Barbieri--Thomassé (arXiv:1507.03369, context only, not
re-read) give an effectively closed strongly aperiodic subshift `Z` over every
finitely generated group with solvable word problem. Every minimal subsystem of
`Z` is free. *Dies at effectiveness.*
- A minimal subsystem is chosen by Zorn, and nothing makes it effectively closed.
- Effectively closed sets of configurations with no computable member exist,
  already for `Z`-subshifts (Cenzer--Dashti--King, context only).
- An effectively closed minimal subsystem would have a computable point by the
  equivalence above.
- The obstruction is to the method, not to (M2).

**Candidate (not attempted).** Effectivize the Gao--Jackson--Seward blueprint
construction of minimal 2-colourings.
- With solvable word problem, balls are computable finite sets, and greedy
  maximal `r`-separated sets along a shortlex enumeration are decidable.
- What must be checked is that the colouring built on these blueprints is a
  computable point with a computable recurrence modulus, and that it is
  hyperaperiodic.

**Attempt 2 (2026-09-17, swarm-0917-w5-pull-bh-3): margin ball-copy
hierarchy.** Stays OPEN. Convention: `(λ.y)(μ) = y(μλ)`, `d(x,z) = |xz^{-1}|`,
copies are right translates `B(ρ)c`.

*Construction.*
- Set `P_0 = 0` on `B(ρ_0)`, and `P_{k+1} = F_k(B(ρ_{k+1}))`.
- `F_j(A)` scans `A` in shortlex order from `1`. It greedily places copies of
  `P_j` at every `c` with `B(ρ_j + m_j)c ⊆ A` and `B(ρ_j)c` disjoint from the
  copies already placed.
- It then runs `F_{j-1}` on the uncovered remainder. `F_{-1}` colours what is
  left by a fixed computable rule that reads only the region's shape.
- With `P_0 = 0` and a zero fill, `y` is constant. The construction is a
  placement skeleton, and Step 3 is exactly where the colours have to come from.
- Parameters: `m_{i+1} > 3(ρ_i + m_i)` and `ρ_{i+1} ≥ 2(ρ_i + m_i)`.
- With a solvable word problem every `P_k` is computable, and `y = lim P_k` is a
  computable point.

*Step 1: central modulus (proved by hand, not written as a node).* Every
`μ ∈ G` lies within `D_i = 2(ρ_i + m_i) + 2ρ_i` of a `P_i`-copy.
- Take the innermost copy `E` of level `≥ i+1` that contains `μ`.
- If `B(ρ_i + m_i)μ` lies in the level-`i` remainder of `E`, greedy maximality
  puts a `P_i`-copy within `2ρ_i`.
- Otherwise push `μ` along a geodesic by `ρ_i + m_i` into the containing copy or
  the gap. The new ball stays within `3(ρ_i + m_i) < m_{i+1}` of that region's
  boundary. Internal copies sit at least `m_{i+1}` inside, so the ball avoids
  them, and maximality applies.
- Consequently `q_r = y|B(r)` recurs in every `(D_i + ρ_i)`-ball once `ρ_i ≥ r`,
  so the orbit closure `X` is minimal, with a *computable central* modulus.

*Step 2: effective closedness. Stops here.*
- (M2) needs `X` effectively closed, which here means the language of `X` is
  decidable, i.e. a computable *global* modulus: every `r`-pattern of `y` occurs
  in every `R(r)`-ball.
- A pattern of `y` at `λ` sits inside `q_{r+|λ|}`, so the central modulus bounds
  its recurrence only in terms of `|λ|`. The method gives no computable bound on
  the `|λ|` by which every `r`-pattern has appeared.
- The unseen patterns are the boundary ones: copies meeting the remainder and
  gap fillings. Their shapes depend on the shapes of large spheres in `G`.
- A sufficient condition is (R_k): every level-`k` patch occurring in `y` occurs
  inside `P_{k+1}`. It is circular, because the boundary patches are created by
  the greedy grouping at levels above `k`.
- *Partial fallback.* `Y_T = {z : q_ρ occurs in every T(ρ)-ball of z, for all ρ}`
  is effectively closed and `X` is its unique minimal subset. `Y_T` is not
  minimal in general, so this does not give (M2).
- No counterexample is claimed: the step is where the method stops, not a
  proven impossibility.

*Step 3: freeness. Not reached; retracted false start.*
- Hyperaperiodicity asks: for `s ≠ 1` there is `R` such that for every `λ` some
  `μ ∈ B(R)` has `y(μλ) ≠ y(μsλ)`.
- *False start.* I first argued that a witness inside a copy `c = aλ` needs
  `P_i(x) ≠ P_i(xt)` with `t = asa^{-1}` and `x = μa^{-1}`, so `|t| ≤ 2ρ_i`. I
  then argued that long conjugators `|asa^{-1}| = 2|a| + |s|` in free groups
  kill this.
- *Why that is wrong.* `x = μa^{-1}` and `xt = μsa^{-1}` both lie within
  `R + |s|` of `a^{-1}`. So `|t| ≤ 2ρ_i` holds automatically whenever `λ` is at
  depth at least `R + |s|` inside the copy. The conjugator length is not an
  invariant. Every `λ` is deep inside the level-`k` copy at `1` for large `k`.
- *What is true.* Descending through the hierarchy, the witness at `λ` becomes a
  local `s`-defect of some `P_j` at the position of `λ`, or at a boundary between
  a level-`j` copy and its remainder.
- So the colouring must give `P_j` local `s`-defects of radius `R(s)`,
  independent of `j`. Near copy boundaries the witnesses must straddle the
  boundary, as in GJS blueprints.
- This is the same shape as the swarm-0917-w5-pull-bh-2 spark. No new
  obstruction is claimed here.

*Resulting decomposition.* (M2) follows from two prerequisites that can fail
independently:
- (a) a computable ball-copy hierarchy with a computable global modulus, i.e.
  (R_k) enforced;
- (b) boundary-straddling hyperaperiodic witnesses placed computably in the same
  hierarchy, i.e. an effective GJS blueprint colouring.

**Attempt 3 (2026-09-17, swarm-0917-w6-w6-bh-last1): margin covering towers
remove the global modulus.** Stays OPEN.

*Established here.* `covering-towers-iff-effective-minimal-free-subshifts`
(complete hand route) proves the following for every f.g. group with solvable
word problem.
- (M2)-type existence is equivalent to a computable tower of finite nonempty
  patch families `L_n` on `B(R_n)`, with `m_n → ∞` and `R_n − m_n → ∞`,
  satisfying:
  - (C) margin covering: every point of `B(R_{n+1} − m_{n+1})` lies within
    `R_n − m_n` of an `L_n`-window of each `L_{n+1}`-patch;
  - (K) containment;
  - (A) local asymmetry.
- The subshift is the explicit set
  `Y = {z : every g has an L_n-window within R_n − m_n}`. It has decidable
  forbidden balls, a computable recurrence radius, and freeness from (A).
- Nonemptiness comes by downward induction.

*Why Attempt 2 stopped where it did.*
- Hierarchies of disjoint copies with gaps cannot satisfy (C) unless `L_n` also
  lists the patches that straddle copy boundaries.
- (K) for those patches is exactly Attempt 2's circular (R_k).
- So decomposition (a) should be replaced by: *build overlapping patch families
  satisfying (C) and (K)*. A computable global modulus is then automatic.
- The freeness "conjugator" issue is a convention artifact, as Attempt 2
  already noted. (A) is a radius-`R(s) + |s|` window condition checked inside
  the patches.

*One-patch extreme (new OPEN premise).*
- `|L_n| = 1` means an overlap-recurrent computable point: the central patch
  `P_n` recurs within `R_n − m_n` of every site. Its orbit closure equals
  `Y_OC`, and (OC) reduces to finite internal checks.
- Recorded as `decidable-groups-have-overlap-recurrent-aperiodic-points`, with
  route `effective-minimal-free-subshifts-via-overlap-recurrence`.

*Where it stops.*
- No tower is constructed over any group without an established (M2) instance.
- *Lemma T.* If the returns of `P_n` contain a subgroup `H_n` with
  `B(R_n)H_n = G`, then `y` is `H_n`-periodic. So subgroup or Toeplitz skeletons
  cannot provide (OC).
- *Numerics over `Z`* (experiments/overlap-recurrence-2026-09-17). (OC) holds
  for Fibonacci and Tribonacci, but fails for Thue--Morse, period doubling and
  Chacon. The one-patch extreme is rigid.
- *The missing step.* Over infinite simple (Kazhdan) inputs, where no
  finite-index skeleton or compact internal model exists, it remains to
  construct computable families satisfying (C) and (K) with (A). This is a
  finite-combinatorics problem on balls, with no limit step left.

**Attempt 4 (2026-09-18, swarm-0917-w7-w7-bh-pull, quantifier-shift): towers
form a Π⁰₁ class, so (M2) = non-effective existence + path selection.** Stays
OPEN.

*Established here.* `tower-classes-are-computably-bounded-pi01-classes`
(complete hand route) says the following. Fix computable radii `R_n` and `m_n`
and a computable asymmetry bound `φ`. Then:
- The set `T_D` of all margin covering towers for these data, computable or
  not, is a computably bounded Π⁰₁ class.
- Every member of `T_D` gives a nonempty minimal free subshift with modulus
  `≤ β_D` and freeness radius `≤ φ`.
- Conversely, every minimal free subshift whose two moduli are computably
  bounded gives a member of some `T_D`.
- (M2)-type existence is exactly a computable member of some `T_D`.

*Resulting decomposition.* (M2) for `Λ` is the conjunction of two parts.
- (N) `free-minimal-subshifts-with-computable-moduli-exist`: some minimal free
  subshift on `Λ`, not necessarily effective, has computably bounded modulus
  and freeness radius. This is equivalent to `T_D ≠ ∅` for some computable `D`.
- *Path selection:* a computable path in such a `T_D`.

(M2) ⇒ (N). So refuting (N) for one `Λ` refutes (M2) by pure dynamics.
- Recorded as route `effective-minimal-free-subshifts-via-tower-class-basis`.
- Its path-selection premise is `nonempty-tower-classes-yield-computable-towers`.

*Class obstruction.* Consider any method that proves only that the tree of
`T_D` is infinite: Zorn inside ABT (Attempt 1), compactness limits (Attempt 2's
partial fallback), local lemma plus compactness (the w5-bh-4 lease), or
genericity.
- Such a method establishes (N) at best.
- It dies at path selection, where the invariant is the Turing degree of the
  chosen path.
- Nonempty computably bounded Π⁰₁ classes without computable members exist
  (context only), so this step is real.
- Methods that survive must build the path level by level with a decidable
  extendability test, or find a path with no branching. The one-patch premise
  `decidable-groups-have-overlap-recurrent-aperiodic-points` is the special case
  `|L_n| = 1`.

*Where it stops.* Neither (N) nor path selection is proved for any group
without a known (M2) instance.
