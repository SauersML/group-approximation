---
rg: 2
id: some-nonsurjunctive-group-gives-a-binary-power-one
kind: claim
title: If some group is not surjunctive over some finite alphabet, then some group is not surjunctive over an alphabet whose size is a power of two
distinct_from:
  some-nonsurjunctive-group-gives-a-binary-one: that asks for the size 2 itself; this accepts any size 2^j, so that claim implies this one, while the converse would need descent from 2^j to 2.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that pushes a failing size to every larger size inside one group; this asks only for one power of two, over any group, so that claim implies this one.
  every-group-is-surjunctive-over-binary-power-alphabets: that is surjunctivity over binary-power alphabets; this is the bridge that turns it into the full conjecture, and the two together are equivalent to the conjecture.
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: if `NS_all` is nonempty, then
`2^j ∈ NS_all` for some `j >= 1`.

**Place in the graph.**
- **The weakest bridge.** With `every-group-is-surjunctive-over-binary-power-alphabets` it gives the conjecture
  (`gottschalk-via-binary-power-nonsurjunctive-witness`). Conversely the conjecture implies it vacuously, so the
  conjecture is exactly this claim together with binary-power surjunctivity.
- **Both recorded bridges imply it.** Upward closure inside one group
  (`binary-power-witness-from-upward-closed-sizes`) and universal binary descent
  (`binary-power-witness-from-binary-witness`). A proof may mix the two moves and change the group.
- **Existentially closed groups.** By `ec-groups-share-the-nonsurjunctive-alphabet-sizes` it says: an existentially
  closed group that is not surjunctive at all fails surjunctivity at some power of two.

## Attempts

- **Moving stars by a reversible binary automaton** (solo follow-up, 2026-09-17). A design that changes an alphabet
  size by adding a star symbol and moves star sets by a bijective `ψ` on `{0,1}^G` is surjective if `ψ`
  preserves the number of non-star sites. Strictness needs a `ψ` that raises that count somewhere and never
  lowers it. By `count-raising-reversible-automata-lower-biased-rokhlin-entropy`, such a `ψ` forces the Rokhlin
  entropy supremum of `G` to be `0`, strictly stronger than the finite bound a strict automaton gives. Such a
  `ψ` also keeps counts 1 and 2. So this class of alphabet changes meets the same entropy barrier as strictness itself. The class is not excluded
  unconditionally.

- **Equivalent odd-part form** (frontier swarm, 2026-09-16). `NS_all` is closed under multiples, so a witness at
  size `k = 2^i m`, `m` odd, gives witnesses at `2^(i') m` for every `i' >= i`. The claim says that the odd part
  `m` can be removed for some `i'`. It is automatic when `m = 1`.
- **Regrouping moves stay inside the radical.** The size moves available without a new idea are multiples
  (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`), passing to an overgroup (`NS(G) ⊆ NS(H)` for `G <= H`),
  and restriction to a subgroup of finite index `m`, which regroups `B^H` as `(B^m)^G` and sends `n ∈ NS(H)` to
  `n^m ∈ NS(G)`. Each move sends `n` to a size whose set of prime divisors contains that of `n`. So from an odd
  failing size they never reach a power of two. A proof must use an alphabet change that is not a regrouping.
- **Linear witnesses.**
  - In characteristic two they give the size `2` (`modular-matrix-failures-descend-to-scalars-over-g-times-p`,
    recorded under `some-nonsurjunctive-group-gives-a-binary-one`), so the claim holds for them.
  - Over `F_p` with `p` odd, the same Maschke descent gives the size `p` over `G × P`. Linear constructions over
    `F_p` only produce sizes `p^d`. The crux is a change of characteristic, which only a nonlinear automaton can
    make.
- **Reserved symbols.** `passive-fixing-injective-automata-are-surjective` applies to every design that pads a
  failing alphabet up to a power of two with reserved symbols. Such a design must write on reserved sites or write
  reserved symbols at unreserved ones.
- **Where it stops.** No construction is known that removes an odd prime from a failing size, for any explicit
  strict table pair, over any group. The frontier notes
  `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md` record the ascent designs tried on the
  way; each one dies at the one-extra-symbol annulus.
