---
rg: 2
id: some-nonsurjunctive-group-gives-a-binary-one
kind: claim
title: If some group is not surjunctive over some finite alphabet, then some group is not surjunctive over two symbols
distinct_from:
  surjunctivity-failure-descends-to-binary-alphabet: that asks for a binary strict automaton over the same group; this allows any group, so that claim implies this one.
  every-group-is-binary-surjunctive: that is binary surjunctivity of every group; this is the bridge that turns it into the full conjecture.
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
  - research/artifacts/gk3-binary-descent-2-2026-09-14.md
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: if `NS_all` is nonempty,
then `2 ∈ NS_all`.

**Place in the graph.**
- It is implied by `surjunctivity-failure-descends-to-binary-alphabet`
  (`universal-binary-descent-from-groupwise-descent`), and vacuously by the conjecture itself.
- With `every-group-is-binary-surjunctive` it gives the conjecture (`gottschalk-via-universal-binary-descent`).
- It is equivalent to binary descent for one existentially closed group, and for every existentially closed
  group (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`).

## Attempts

- **Reserved-symbol extensions are dead** (`passive-fixing-injective-automata-are-surjective`, 2026-09-14).
  An injective automaton that leaves a reserved set of symbols in place and writes no reserved symbol at an
  unreserved site is surjective, over every group. A binary coding of a strict automaton must write on
  reserved sites, or write reserved symbols at unreserved ones.
- **Products with a finite group** (artifact Section 4, 2026-09-14).
  - Binary automata over `G × F` are automata on `({0,1}^F)^G` commuting with fiber translation, and local
    phase normalization is always available.
  - The natural design uses default symbols for invalid cells, carries the phase on relay `1`, and tags
    invalid demanded cells. It runs out of free orbits: `k (N - k + 3) > N`.
  - By the barrier, any binary strict automaton over `G × F` must rewrite a constant fiber, or make a
    non-constant fiber constant.
- **Not tried:** phase-borrowing between relays, overgroups of finite index with outer action, and group
  change beyond finite index (artifact Section 5).
- **Linear witnesses descend** (`modular-matrix-failures-descend-to-scalars-over-g-times-p`, 2026-09-14).
  `M_n(F_p[G])` fails direct finiteness iff `F_p[G × P]` does for some finite `P` with `p ∤ |P|`, e.g.
  `P = C_q^r ⋊ C_r` with `r >= n`. With `linear-strict-pairs-are-transposes-of-post-surjective-automata`, a
  strict automaton linear over a field of characteristic two gives a binary strict automaton over `G × P`
  with `|P|` odd. So this claim holds for linear witnesses, and for homomorphic witnesses over 2-group
  alphabets (`homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness`). Nonlinear witnesses remain.
- **Odd fibers leave one reserved symbol** (`binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`).
  For `|P|` odd, `{0,1}^(G×P) ≅ {0,1}^G × I_P^G`, and a `P`-equivariant strict automaton on `I_P^G`
  suffices. The two constant fibers become the single zero vector. For `P = C_q` the condition is a strict
  automaton on `R_q^G`, `R_q = F_2[x]/(Φ_q)`, whose rule commutes with multiplication by `ζ = [x]`.
- **Phase-borrowing and outer action** (`research/artifacts/gk3-binary-descent-2-2026-09-14.md`, Sections
  5–6). Output phases are already spent transporting input phases, and relative-phase tags must be
  coboundaries, so they add no room to the Section 4.3 design. Overgroups `G ⋊ P` split the same way, with
  `0` still the only fixed symbol.
- **Compression criterion** (same artifact, Section 2). An injective automaton from a full shift on at least
  three symbols into the binary full shift, over some group, gives a binary strict automaton there.
