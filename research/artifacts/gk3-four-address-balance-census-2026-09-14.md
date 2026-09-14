# Four-address binary balance census (lane gk3-bernoulli-preservation, 2026-09-14)

**Target.** `binary-four-address-injective-automata-have-balanced-rules` (OPEN), a case of
`every-injective-ca-has-uniform-single-site-output-law`. Over every group, an injective two-symbol automaton with
four memory elements should have a balanced rule. An unbalanced injective rule over any group refutes Gottschalk's
conjecture.

**Status of this artifact: INTERIM.**
- The single-flip census and its independent control are complete.
- The exact triage of table groups, and the perturbation refinement for the rules that survive single flips,
  are running on MSI (job 792117). Section 6 will be replaced with the final counts.
- No claim node has landed yet.

Code and data: `experiments/gottschalk-four-address-balance/`.

## 1. Setting and reductions

- **Setup.** `G` a group, `M = {m_0, m_1, m_2, m_3}` four distinct elements with `m_0 = 1`, and
  `mu : {0,1}^M -> {0,1}`, with `tau(x)(g) = mu((x(g m_i))_i)`.
- **Balance.** `mu` is balanced iff it has eight preimages of `1`. Under uniform input the site law of `tau` is
  uniform iff `mu` is balanced.
- **Reductions** (Section 1 of `small-memory-balance-census-2026-09-12.md`):
  - a rule ignoring a coordinate lives on at most three addresses, and
    `three-address-binary-injective-rules-are-balanced` applies;
  - translation (`m_0 = 1`) and restriction to `H = <M>`;
  - symmetries: address permutations, global input complement, output complement;
  - **(R5)** if `<M>` is amenable, an injective `tau` is bijective (Gromov–Weiss), hence balanced.
- **Constant test (C1).** Injectivity forces `mu(0000) != mu(1111)`.
- **Counts.** There are 859 unbalanced rule classes up to symmetry. 401 pass C1, and 394 of those read all four
  coordinates.

## 2. Single invisible flips as a CSP on the quotient partition

Flip `x` at `h`. The output sites that see the change are `h m_i^-1`. At `h m_i^-1` coordinate `i` reads `x(h)`,
and coordinate `j != i` reads `x(h q(i,j))` with `q(i,j) = m_i^-1 m_j`. The flip is invisible iff some values on
the sites `h q(i,j)` make coordinate `i` blind at every `h m_i^-1`.

- **The instance depends only on the quotient partition.** Two context sites coincide iff their quotients
  coincide in `G`, and no context site equals `h`.
- **Admissible partitions.** They are stable under `(i,j) -> (j,i)`, and never merge `(i,j)` with `(i,k)` or
  `(j,i)` with `(k,i)` for `j != k`, since either would force `m_j = m_k`. There are 1124 (`flip1.py`).
- **Monotonicity.** Coarsening adds constraints. So for each rule the failing partitions are up-closed and
  determined by their minimal elements.
- **Result (MSI job 781776, `flip1.json`).** 86 of the 394 rule classes have an invisible single flip on every
  admissible partition. So those 86 are never injective, over any group. 969 distinct partitions occur as
  minimal failing partitions of the remaining rules.

## 3. Exact triage of table groups

For a minimal failing partition `P`, the table group is
`G_P = <a, b, c | q(rep)^-1 q(p) = 1 for p ~ rep>`, with `m_1, m_2, m_3 = a, b, c`. Every group whose memory
realizes a coarsening of `P` has a memory group that is a quotient of `G_P`.

**Decision procedure** (`analyze2.py`, `gp.py`). Each step is exact.
- Tietze elimination of a generator occurring once in a relator, then Nielsen moves up to depth three. After
  each move, relators are reduced modulo the orders forced by pure-power relators.
- **Free products of cyclic groups** (trivial, cyclic, free, `Z/2 * Z/2`, ...). The word problem is the syllable
  normal form.
  - Amenable iff at most one nontrivial factor, or exactly `Z/2 * Z/2`.
- **Graph products of cyclic groups.** All non-power relators are commutators `[g^e, h^f]` with `e`, `f`
  generating `<g>`, `<h>`.
  - *Amenability criterion.* Amenable iff every component of the non-commutation graph is one vertex, or two
    vertices of order 2.
  - *Why.* Special subgroups embed. Two non-commuting vertices give `G_u * G_v`, and a non-commuting path
    `u - v - w` gives `(G_u x G_w) * G_v` or `G_u * G_v * G_w`. All of these are non-amenable except `Z/2 * Z/2`.
  - *Word problem.* Merge same-generator syllables separated by commuting syllables, then take the greedy
    lexicographic shuffle representative (Green's normal form theorem).
- **Cyclic-by-cyclic.** On two generators, a relator `h^-1 g h g^(-+1)` makes `<g>` normal with cyclic quotient,
  so the group is amenable.
- **Finite groups.** Otherwise, coset enumeration with two strategies, at most 3000 cosets and equal orders. A
  complete table proves finiteness.
- **Otherwise undecided.** Such a partition counts as not excluded.

**Exclusion principle.** A rule is excluded over every group when each of its minimal failing partitions has an
amenable table group or a collapsing memory. Then either a single invisible flip exists, or `<M>` is amenable and
(R5) gives balance. The procedure only ever errs toward keeping a rule; it never excludes one wrongly.

## 4. Perturbation refinement for survivors

A state is a relator set `R`. For an open state we flip `F = {1}` or `F = {1, g}`, with `g` a quotient or a
product of two quotients, and solve invisibility exactly in `G_R`. Every candidate flip is invisible for these
four coordinates in `G_R`.

- **Merges that can break a solution in a group realizing `R`:**
  - (i) two context sites carrying different bits;
  - (ii) a context site with a flipped site;
  - (iii) two output sites.
- **Recursion.** Each merge is one extra relator. The failing groups are covered by the extended states, which
  are decided and refined recursively, with memoization, depth at most three and a global state budget
  (`dflip.py`).
- **Closure.** A rule closes when every branch reaches an amenable or collapsing group.

## 5. Independent control of the single-flip census

`control1.py` shares no code with `flip1.py`.
- **Groups.** It builds multiplication tables for `Z/7`, `Z/12`, `D_5`, `D_8`, `A_4`, `S_4`, `A_5`, `Q_8` and
  `S_3 x S_3`, and checks each group's order.
- **Sampling.** 12 random placements containing `1` per group, and 8 random rules per placement.
- **Test.** It enumerates every assignment on the context set with `x = 0` elsewhere, and compares `tau(x)` and
  `tau(x')` at every element of the group.
- **Result (MSI job 791356, `control1.out`).**
  - 864 of 864 verdicts agree with `flip1.py` on the realized partition.
  - Every realized partition occurs in the admissible list.

### 5b. Consistency control of the table-group triage

`control2.py` (MSI job 792968, `control2.out`) re-derives the triage of `analyze3.json` through a second entry point
(`dflip.make_nf`), which runs its own Nielsen search.
- **Substitution tracking.** For all 826 partitions with a normal form on both paths, every original relator of
  `G_P` is trivial in the recognized normal form. So the tracked substitution really defines a homomorphism from
  `G_P`.
- **Flags.** On those 826 partitions the amenable flag and the memory-distinct flag agree between the two paths.
- **Cyclic-by-cyclic.** On 27 partitions the second path reached cyclic-by-cyclic form, and `analyze3` also marks
  them amenable. No contradiction.
- **Finite groups.** All 36 finite orders are re-derived by both coset-enumeration strategies.

The two paths share the elimination and recognition code. So this checks consistency and substitution tracking, not
independent group theory.

## 6. Results so far (INTERIM)

**Second triage pass** (job 792117 stage one, `analyze3.json`), with graph products and cyclic-by-cyclic groups
recognized:
- **199 of the 394 rule classes are excluded over every group, and 195 survive.**
- The 969 minimal failing partitions decide as follows.

  | table group | amenable | non-amenable | undecided |
  |---|---|---|---|
  | free products of cyclics | 624 | 131 | |
  | graph products of cyclics | 85 | 13 | |
  | cyclic-by-cyclic | 61 | | |
  | finite | 36 | | |
  | `Z^2` | 3 | | |
  | other | | | 16 |

- **Survivors.** 160 distinct partitions block the 195 surviving rules: 131 non-amenable free products of
  cyclics, 13 non-amenable graph products and 16 undecided. They have between 7 and 11 quotient classes, so at
  most five coincidences among the twelve memory quotients.
- Only 3 surviving rules are blocked solely by undecided groups.

**First triage pass** (job 790868), before graph products and cyclic-by-cyclic groups were recognized:
- 183 of the 394 rule classes excluded over every group, 211 surviving;
- of the 969 minimal failing partitions:
  - amenable: 121 finite, 638 free products of cyclics, 3 `Z^2`;
  - 131 non-amenable free products of cyclics;
  - 76 undecided.
- Undecided survivors include:
  - Klein-bottle groups and other cyclic-by-cyclic groups (amenable);
  - `Z * (Z/2)^2` and right-angled Coxeter groups with a non-commuting path (non-amenable);
  - `Z`-by-`D_infinity` examples (amenable; not yet recognized automatically).
- Sanity checks of the decision code on known cases:
  - `{1, a, b, ab}` gives `F_2`;
  - `a^2 = 1` gives `Z/2 * F_2`;
  - several partitions give `D_infinity`, and one gives `Z x Z/2`.

Final counts, survivor list and refinement outcome: pending job 792117.
