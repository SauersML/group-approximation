---
rg: 2
id: every-countable-group-embeds-in-an-orbit-finite-fp2-affine-actor
kind: claim
title: "Every countable group embeds in a semidirect product S ⋊ W of type FP_2 whose automorphism group W is finitely generated with finitely many orbits on S"
distinct_from:
  decidable-groups-embed-in-orbit-finite-affine-actors: that asks for a finitely presented S ⋊ W, so only inputs with solvable word problem qualify; this asks for type FP_2, which admits every countable input because S ⋊ W need not be recursively presented.
  every-countable-group-lies-in-a-faithful-ha2-actor: that asks for any faithful [HA_2] overgroup; this asks for an affine one, which implies that by `orbit-finite-fp2-affine-actors-are-faithful-ha2-actors`. The converse is not known.
  every-countable-group-embeds-in-an-fp2-group: that is Leary's FP_2 envelope with no action condition; this adds an orbit-finite automorphism group on a normal factor.
---

**OPEN.** For every countable group `G` there are a group `S` and a finitely
generated `W ≤ Aut(S)` such that `G` embeds in `Γ = S ⋊ W`, `Γ` is of type FP_2,
and `W` has finitely many orbits on `S`.

Route into Problem 1.25: `faithful-ha2-actor-via-orbit-finite-fp2-affine-actors`.

**Screens** (each proved in the cited claim or immediate):

- `W` is a retract of `Γ`, so `W` is of type FP_2 (retracts of FP_2 groups are
  FP_2; Bieri's notes, not re-verified here), and `S` has finitely many element
  orders (`conjugacy-finite-actors-have-finitely-many-element-orders`).
- An input `G` with infinitely many element orders needs them in `G/(G ∩ S) ≤ W`;
  the inner choice `W = Inn(S)` is then excluded.
- There is no computability screen: groups of type FP_2 need not be recursively
  presented (Leary's `J(l,S)`, recorded on `every-countable-group-embeds-in-an-fp2-group`),
  so inputs with unsolvable word problem are not excluded. Passing from type (A)
  to type FP_2 is meant to remove exactly that screen.
- `W` acts faithfully on `S`, so finite `S` forces finite `W`; an infinite input
  needs `S` infinite.
- `Γ` is finitely generated, so `S` is finitely generated as a group with
  `W`-operators.

**Test cases, by increasing difficulty.**

1. Finite `G`: settled. Any finite `Γ` is of type FP_2; take `S = Sym(G)` for
   `|G| ≥ 3` (trivial centre) and `W = Inn(S)`, so `Γ ≅ S × S ⊇ G`.
2. Torsion-free `G` of type FP: the inner case `W = Inn(S)` with `S` torsion-free,
   conjugacy-finite and FP_2 is exactly
   `torsion-free-fp-groups-embed-in-fp2-conjugacy-finite-groups`.
3. `G = Q/Z`: the inner case is excluded, and `W` must contain a copy of `Q/Z`:
   `G ∩ S` has bounded orders, so it is finite cyclic, and `Q/Z` modulo a finite
   subgroup is again `Q/Z`, embedded in `W`. A candidate shape: `W` an FP_2 overgroup of `Q/Z` (one exists by
   Leary) and `S` an infinite `F_p W`-module, finitely generated as a module, with
   finitely many `W`-orbits on its vectors, such that `S ⋊ W` is FP_2. Whether any
   FP_2 group `W ⊇ Q/Z` has such a module is the first open question on this node.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-z-last1, reframing): node created. The three
  test cases above are the first falsifiable steps. Case 3 is the first place the
  affine route could die for a reason the inner route does not already have.
