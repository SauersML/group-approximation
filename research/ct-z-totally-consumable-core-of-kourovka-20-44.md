---
rg: 2
id: ct-z-totally-consumable-core-of-kourovka-20-44
kind: claim
title: "The totally consumable core of Kourovka 20.44: finitely many orbits always implies total consumability; on a positive ray the converse holds; for Kohl's G_T the converse is equivalent to the 3x+1 map having finitely many components; so 'totally consumable ⇒ finitely many orbits' is the Collatz/Mahler-type core"
distinct_from:
  ct-z-frozen-tails-anywhere-give-kourovka-20-44: that reduces 20.44 to totally consumable (TC) groups; this records what is known about the TC class itself.
---

**ESTABLISHED** for items 1–3 (lane proof, elementary, not reviewed). The TC conjecture below is
**OPEN**. Kourovka 20.44 (S. Kohl) stays OPEN.

## Statement

For finitely generated `G ≤ CT(Z)`, totally consumable (TC) means that no point of `Ẑ` has a
frozen degree (`ct-z-frozen-tails-anywhere-give-kourovka-20-44`).
1. **Finitely many orbits ⇒ TC.** A frozen degree anywhere makes `Y_K` a nonempty union of classes.
   By the uniform count, `G` then has infinitely many orbits.
2. **Positive ray: TC ⇔ finitely many orbits ⇔ no frozen tail.** If `Λ(G) = Zv` with `v ≥ 0`,
   the corner argument (`ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`, item 1) puts a
   point of every orbit in `[−Π^D, Π^D)`.
3. **Dimension two is Collatz.** Kohl's `G_T` is TC (frozen-tails node, corollary). It has
   finitely many orbits iff the 3x+1 map has finitely many components on `Z`
   (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`). So the implication "TC ⇒ finitely many
   orbits" is, already at `G_T`, a finiteness statement for 3x+1.

**TC conjecture.** Every TC finitely generated subgroup of `CT(Z)` has finitely many orbits on `Z`.
- By the frozen-tails node it implies Kourovka 20.44.
- It holds on positive rays (item 2).
- At `G_T` it is equivalent to 3x+1 having finitely many components.

## Why trapped and dimension-1 TC groups resist

- **Trapped slope lattices** (cone-avoiding, e.g. `(3/2)^Z` or `⟨3/2, 5/2⟩`).
  - A zero tail of `x` at degree `K` is read somewhere on the boundary of its finite level set
    `{w·p = w·K}`. The configuration there is only bounded by `m_p`.
  - On that simplex `log m_p` is linear in `p`, so the boundary contains the maximizing vertex,
    where `m_p ≥ m_K > x`.
  - Total consumption therefore forces no descent. Proving one is a Mahler-type 3/2 question about
    where drift walks on level sets exit.
- **Dimension one with rank at least two** (e.g. slopes `2` and `3/5`).
  - Tubes along the ray can be read at their transversal ends at any depth.
  - Their trapped subgroups are trapped groups, so settling dimension one is at least as hard as the
    trapped case.

## Lesson for general BH

**The whole difficulty of arithmetic orbit problems sits in one dynamical class: groups that read
every depth from every point.**
- Frozen information, the positive-ray corner, and holonomy at attractor–repeller pairs are all
  mechanisms for leaving that class or controlling it.
- What remains inside it is exactly 3x+1-type or Mahler-3/2-type exit behaviour.
- A host construction that must control orbits of an embedded subgroup should keep the subgroup
  out of the TC class, or on a positive ray.
