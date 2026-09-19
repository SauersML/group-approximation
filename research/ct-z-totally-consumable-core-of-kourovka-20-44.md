---
rg: 2
id: ct-z-totally-consumable-core-of-kourovka-20-44
kind: claim
title: "The totally consumable core of Kourovka 20.44: finitely many orbits always implies total consumability; on a positive ray the converse holds; for Kohl's G_T the converse is equivalent to the 3x+1 map having finitely many components; so 'totally consumable ⇒ finitely many orbits' is the Collatz-type core, with a Mahler-type 3/2 analogy on trapped lattices (heuristic)"
distinct_from:
  ct-z-frozen-tails-anywhere-give-kourovka-20-44: that reduces 20.44 to totally consumable (TC) groups; this records what is known about the TC class itself.
---

**ESTABLISHED** for items 1–3 (lane proof, elementary; **Referee PASS** bh-ref-q11 2026-09-19 for items 1–3; the Mahler-type discussion is heuristic). The TC conjecture below is
**OPEN**. Kourovka 20.44 (S. Kohl) stays OPEN.

## Statement

For finitely generated `G ≤ CT(Z)`, totally consumable (TC) means that no point of `Ẑ` has a
frozen degree (`ct-z-frozen-tails-anywhere-give-kourovka-20-44`).
1. **Finitely many orbits ⇒ TC.** A frozen degree anywhere makes `Y_K` a nonempty union of classes.
   By the uniform count, `G` then has infinitely many orbits.
2. **Positive ray: TC ⇔ finitely many orbits ⇔ no frozen tail.** If `Λ(G) = Zv` with `v ≥ 0`,
   the corner argument (`ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`, item 1) puts a
   point of every orbit in `[−Π^D, Π^D)`.
3. **Dimension two is Collatz.** Kohl's `G_T` is TC, because every transversal of `G_T` has density zero (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`), which rules out a frozen tail by the frozen-tails node. It has
   finitely many orbits iff the 3x+1 map has finitely many components on `Z`
   (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`). So the implication "TC ⇒ finitely many
   orbits" is, already at `G_T`, a finiteness statement for 3x+1.

**TC conjecture.** Every TC finitely generated subgroup of `CT(Z)` has finitely many orbits on `Z`.
- By the frozen-tails node it implies Kourovka 20.44.
- It holds on positive rays (item 2).
- At `G_T` it is equivalent to 3x+1 having finitely many components.

## Why trapped and dimension-1 TC groups resist (heuristic)

This section gives analogies, not reductions. No trapped TC group is shown to encode a Mahler-type question. Nor is dimension one shown to be as hard as the trapped case, since TC and orbit finiteness do not pass automatically between a group and its subgroups.


- **Trapped slope lattices** (cone-avoiding, e.g. `(3/2)^Z` or `⟨3/2, 5/2⟩`).
  - A zero tail of `x` at degree `K` is read somewhere on the boundary of its finite level set
    `{w·p = w·K}`. The configuration there is only bounded by `m_p`.
  - On that simplex `log m_p` is linear in `p`, so the boundary contains the maximizing vertex,
    where `m_p ≥ m_K > x`.
  - Total consumption therefore forces no descent. Proving one looks like, by analogy, a Mahler-type 3/2 question about
    where drift walks on level sets exit.
- **Dimension one with rank at least two** (e.g. slopes `2` and `3/5`).
  - Tubes along the ray can be read at their transversal ends at any depth.
  - Their trapped subgroups are trapped groups, so heuristically dimension one contains the difficulty of the
    trapped case.

## Lesson for general BH

**The whole difficulty of arithmetic orbit problems sits in one dynamical class: groups that read
every depth from every point.**
- Frozen information, the positive-ray corner, and holonomy at attractor–repeller pairs are all
  mechanisms for leaving that class or controlling it.
- What remains inside it is 3x+1-type behaviour (proved at `G_T`) and, by analogy, Mahler-3/2-type exit behaviour.
- A host construction that must control orbits of an embedded subgroup should keep the subgroup
  out of the TC class, or on a positive ray.

## Referee (bh-ref-q11, 2026-09-19): PASS for items 1–3; the "resist" section and "Mahler-type" are heuristic

**Items 1–3: correct.**
- **Item 1** is the contrapositive of item 1 of the frozen-tails node, which I refereed PASS (643914a82b). A frozen degree gives a nonempty clopen `Y_K`, which contains infinitely many integers. Each orbit meets it at most `A_K` times, so there are infinitely many orbits.
- **Item 2.**
  - TC means no point of `Ẑ` has a frozen degree. So every non-consumable set `C_K^c`, a union of classes, is empty, and every `δ_s = 0`.
  - Item 1 of `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44` (Referee PASS, bh-ref-kourovka-a) then gives at most `2Π^D` orbits.
  - With item 1 this gives the equivalence. "TC ⇔ no frozen tail" is the definition.
- **Item 3.**
  - `G_T` is TC, since a frozen tail would give linearly many orbits, against `ν_(G_T)(N) = o(N)`.
  - `G_T` has finitely many orbits iff the 3x+1 map has finitely many components on `Z` (item 2 of the Collatz-hardness node).
  - So at `G_T`, "TC ⇒ finitely many orbits" is exactly that open 3x+1 finiteness statement.
- **The TC conjecture** is correctly labelled OPEN. At `G_T` it is equivalent to 3x+1 finiteness on `Z`, so it is at least that hard.

**"Why trapped and dimension-1 TC groups resist": heuristic, and should be labelled so.**
- The vertex estimate is correct: `log m_p` is linear on the level simplex, so it is maximised at a vertex with `m_p ≥ m_K > x`.
- But "total consumption forces no descent", and its identification with Mahler's 3/2 problem, are analogies, not reductions. No trapped TC group is shown to encode a Mahler-type question.
- "Settling dimension one is at least as hard as the trapped case" is also unproved: TC and orbit finiteness do not pass between a group and its subgroups automatically.
- So the title's "Collatz/Mahler-type core" is proved on the Collatz side (`G_T`) and heuristic on the Mahler side.
