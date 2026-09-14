# sk-strong-8 plan (free taste; findings that change the note's headline)

Lane sk-strong-8, 2026-09-13 ~20:30 CDT. Wave 8 explorer (ROSTER-F).

## Target
One theorem that can replace the note's two headline items, "G_X is a limit of finite simple expanders"
(rev2, Theorem 1) and "LEF iff subgroup of a simple Kazhdan LEF group" (rev3 §2), by a single statement:

> A finitely generated group is LEF if and only if it is a subgroup of an infinite, finitely generated,
> simple group with property (T) that is the limit, in the space of marked groups, of finite simple groups
> SL_N(F_2) whose Cayley graphs form expanders.

## Why it changes the headline
- It matches the title on main ("Infinite simple Kazhdan groups that are limits of finite simple groups").
- The abstract becomes one sentence of mathematics: approximation by finite groups is exactly the
  class of subgroups of simple Kazhdan limits of finite simple expanders. Ozawa's question is the case of
  the trivial group.

## What is missing on main
- `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` uses models on `2^(Q_n) × Q_n`. Their generated
  algebra commutes with right translations by Q_n, so it is not a full matrix algebra, and the approximants are not
  simple groups.
- `finite-simple-groups-converge-to-simple-kazhdan-group` is only for subshift groups G_X over Z.

## Method
- Use the "view" models on `F_2[F_2^(Q_n)]`, configurations seen from the base point: Q_n permutes coordinates,
  the flip translates by 1_e, and letter indicators are diagonal.
- Conjugates of the letter indicator separate configurations, and the translations are transitive. So the
  free algebra maps ONTO M_(2^|Q_n|)(F_2), and EL_3 of the ring's free cover maps onto SL_(3·2^|Q_n|)(F_2).
- Injectivity on fixed elements for all large n comes from a cylinder chosen off the fixed-point sets
  (topological freeness). Marked convergence follows, and EJZ (T) of EL_3 over the free algebra gives
  uniform expansion.

## Not duplicated
sk-lef-embedding-c/e and sk-universal-embedding-a/b own the LEF host and its note text, and sk-expanders-limits owns
the Z case. This lane adds only the finite simple limit property of the host and the combined characterization.

## Deliverables
Claims with complete routes, an artifact with full proofs, a §6 proposal, and review queued with sk-verify-7.
