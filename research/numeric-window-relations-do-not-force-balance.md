---
rg: 2
id: numeric-window-relations-do-not-force-balance
kind: claim
title: Window fiber counts used only as numbers force a uniform site law over amenable decoder memory groups and never over nonamenable ones at large alphabets
invalidates: [balance-from-numeric-window-relations]
distinct_from:
  decoder-window-fiber-bound-loses-exactly-the-boundary: that proves the decoder fiber bound and its boundary loss for one automaton; this shows no argument from that bound, translation invariance, integral finitely dependent counts and a zero removes the loss, since unbalanced measures satisfy all of them over every nonamenable decoder memory.
  finite-left-inverse-identity-does-not-force-balance: that is a fact about the end-fixing tree, an index set that is not a group acting on itself, where counts obey totals and invariance but reads are not right-cancellative; this keeps the discrete group law and still exhibits imbalance, so what is missing is not a numerical relation.
  amenable-decoder-memory-forces-surjectivity: that derives surjectivity from the pointwise decoder identity when the decoder memory group is amenable; this shows the numerical shadow of the identity already gives a uniform site law there and gives nothing once that group is nonamenable.
artifacts:
  - research/artifacts/numeric-window-relations-no-go-2026-09-12.md
---

**ESTABLISHED** by `numeric-window-relations-do-not-force-balance-proof` (artifact Sections 1–3).

Let `G` be a group, `A` an alphabet with `q` symbols, `mu` the uniform product measure, and `M`, `N` finite
sets containing `e`. For finite `E` put `int_N E = {g : gN is contained in E}`. A probability measure `nu`
on `A^G` satisfies the *numerical window relations* for `(M, N)` if:

- **(R1)** `nu` is shift-invariant;
- **(R2)** `q^|EM| nu[p]_E` is an integer for all finite `E` and `p in A^E`, and the restrictions of `nu` to `U` and `U'`
  are independent whenever `UM` and `U'M` are disjoint;
- **(R3)** `nu[p]_E <= q^(-|int_N E|)` for all finite `E` and `p`;
- **(R4)** some cylinder is `nu`-null.

The image of `mu` under a strict automaton with memory `M` and left-inverse memory `N` satisfies them.

1. **Amenable decoder memory.** If `N` generates an amenable subgroup, R1 and R3 force a uniform one-site law.
2. **Nonamenable decoder memory, large alphabets.**
   - If `N` generates a nonamenable subgroup, there is `theta_N < 1` with `|int_N E| <= theta_N |E|` for every
     finite `E`.
   - Take `q >= 3` with `q^(1 - theta_N) >= 2`, and the merge rule `f(a_2) = a_1` (every other symbol fixed).
     The iid image of `mu` under `f` satisfies R1–R4 for every `M`, and its site law is not uniform.
3. **Binary alphabet.** Take `q = 2`. Let `c` have infinite order, and let `N` contain the radius-2 ball of a
   free pair `a, b`. The image of `mu` under the AND rule `x(g) x(gc)` satisfies R1–R4 for `M = {e, c}`, with
   site law `(3/4, 1/4)`.

4. **The Gibbs bridge relations too** (artifact Section 4, Theorem 6).
   - Setup: `M` and `N` generate nonamenable subgroups, and `q = r^k` with `k >= 1/(1 - theta)`, where
     `theta` is the larger interior density of `N` and `M^-1`.
   - The measure: the image of `mu` under `(b_1, ..., b_k) -> (b_1, ..., b_(k-1), b_0)`, applied sitewise.
   - What it satisfies: R1–R4, and every relation of
     `research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md`. Its support is a
     shift of finite type with this measure as its unique uniform Gibbs measure; exact finite-range weak
     mixing holds; completion counts satisfy `N_Y(E, c) = q^|I_E| b_E(c)` with `b_E(c)` a positive integer;
     and `q^|I_E| <= N_Y(E, c) <= q^|E|`.
   - Its site law is not uniform.

**Consequence.** At the alphabet sizes and decoder memories of cases 2–4, no argument from these numerical
relations proves a uniform site law, so none proves balance at any window. Here "numerical relations"
means exactly R1–R4 and the Gibbs-bridge relations of part 4. At `q = 4` it also means the pushforward
relation of `research/artifacts/gk-vf-positive-b-verification-2026-09-12.md` §3.6: the merge measure is an
automaton image of `mu`, and some automaton carries it back to `mu`. A numerical proof of the goal handles
every alphabet directly, so it would have to work at the sizes of cases 2 and 4. That does not apply to a
proof that reaches small alphabets numerically and then passes through an alphabet reduction (below).

At those alphabet sizes and decoder memories, this covers the following manipulations of window counts and
completion counts:
- mass transport along the decoder graph;
- averaging over translates or invariant random windows;
- cofinal window families;
- local permutations of the image;
- telescoping `tau`, `sigma`, `tau` at the level of counts.

**Inputs not shown consistent with imbalance** (artifact Section 5). This is a classification of the inputs
examined so far, not a theorem about all proofs.
- **The pointwise decoder identity `sigma o tau = id`, on the group's own coincidence pattern.** Without the
  group law this identity coexists with imbalance, on the end-fixing tree
  (`finite-left-inverse-identity-does-not-force-balance`, a tree fact only).
- **Maximal Bernoulli Rokhlin entropy.** The conjugacy-entropy proof of balance factors through it.
- **A direct lower bound on `h_fin`** (`injective-ca-images-have-full-single-site-entropy`). INF implies it,
  and it is a priori weaker.
- **Small alphabets plus an alphabet reduction.** Cases 2 and 4 need large `q`, and case 3 needs a free
  radius-2 ball in the decoder memory. A numerical proof at `q = 2` for decoder memories outside case 3 is
  not excluded. Combined with a descent landing in that class, it would reach every alphabet. The descent
  `surjunctivity-failure-descends-to-binary-alphabet` is OPEN and changes memories.
