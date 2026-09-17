---
rg: 2
id: recurrent-orbits-force-z3-meet-stabilizer-proof
kind: route
title: Push the Schreier graph of a subgroup into the ambient Schreier graph along shortest paths; it is a rough embedding, and a free Z^3-orbit is the transient lattice
target: recurrent-orbits-force-every-z3-to-meet-the-stabilizer
requires:
  - lyons-peres-energy-rough-embedding-and-polya-transience
---

Imports (verbatim in `lyons-peres-energy-rough-embedding-and-polya-transience`):
Theorem 2.17 (a rough embedding from a transient network makes the target
transient), and Pólya (the nearest-neighbour graph of `Z^3` is transient). Networks may
have multiple edges and loops, and loops "may be ignored". So we delete all loops, and
a conductance `c(y, y′) = k` means `k` parallel edges of resistance `1`.

**Part 1.** Let `L = max_{t ∈ T} |t|_S`, the longest `S`-word length of a generator
in `T`, and let `m = |S|`.

- *The map.* Take `ϕ : K·x → G·x` to be the inclusion.
- *Edge paths.* An edge of `Sch(K·x, T)` comes from some `t ∈ T` and a vertex `y`
  with `ty ≠ y`. Send it to a shortest oriented path in `Sch(G·x, S)` from `y` to
  `ty`. Such a path is nonempty (its endpoints differ), simple (it is shortest) and of
  length at most `L`. Pair `t` with `t^{-1}`, and send the reverse edge to the
  reversed path. So condition (i) holds with `α = L`.
- *Overlap.* Suppose an edge `e′` of `Sch(G·x, S)` lies on the path of the edge
  `(y, t)`. Then `y` is within distance `L` of the tail of `e′`. Every vertex has at
  most `m` edges, so there are at most `(m+1)^L` such `y`, and `|T|` choices of `t` for
  each. So condition (ii) holds with `β = |T|(m+1)^L`.
- *Conclusion.* `ϕ` is a rough embedding. If `K·x` is transient, Theorem 2.17 makes
  `G·x` transient.

Taking `K = G` with two generating multisets, in both directions, gives independence
of `S`. The last sentence of Part 1 is the contrapositive.

**Part 2.** Let `y ∈ G·x`, and suppose `A ∩ G_y = 1`, where `A = ⟨a_1, a_2, a_3⟩ ≅ Z^3`.

- *The orbit is the lattice.* The map `Z^3 → A·y`, `n ↦ a_1^{n_1} a_2^{n_2} a_3^{n_3} y`,
  is a bijection. Take `T = (a_1^{±1}, a_2^{±1}, a_3^{±1})`. The edges of
  `Sch(A·y, T)` join `n` to `n ± e_i` with conductance `1`. This is the
  nearest-neighbour graph of `Z^3`, which is transient by Pólya.
- *Contradiction.* By Part 1 with `K = A` and base point `y`, `G·y = G·x` is
  transient. This contradicts recurrence. Hence `A ∩ G_y ≠ 1`. ∎
