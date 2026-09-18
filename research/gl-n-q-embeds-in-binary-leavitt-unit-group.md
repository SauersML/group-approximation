---
rg: 2
id: gl-n-q-embeds-in-binary-leavitt-unit-group
kind: claim
title: For every n >= 2 the group GL_n(Q) embeds, as an abstract group, in the unit group of the binary Leavitt algebra over F_2
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for some finitely presented simple host; this names one candidate host, the unit group of L_(F_2)(1,2), which is finitely presented by import and simple.
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that embeds GL_n(A) for unital subalgebras A of L_(F_2)(1,2), so only groups linear in characteristic two; GL_n(Q) is not of that form for commutative A (Attempts), so this asks for a non-linear embedding.
  leavitt-unit-centralizers-have-finite-rank: that conjecture would refute this claim (through rationals-do-not-embed-in-binary-leavitt-unit-group); this is the positive embedding question it would settle.
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `U = R^x`. For every `n >= 2` there is an injective group homomorphism
`GL_n(Q) -> U`.

**Why this host.** `U` is finitely presented (`leavitt-unit-group-finitely-presented`, a literature import of
Khanh arXiv:2609.08428v1, Theorem 6.1, not reviewed here) and simple (`binary-leavitt-unit-group-is-simple`).
So this claim settles `gl-n-q-embeds-in-fp-simple-group` (route `gl-n-q-bh-via-binary-leavitt-unit-group`).
No copy of `Q` inside `R` is needed: `R` has characteristic two, and the embedding only has to be one of groups.
The root node's obstructions O2 and O3 concern `V` and `VA` and say nothing about `U`.

## What an embedding must supply

- **Divisibility.** The unipotent subgroup `(Q,+)` has to go to units of infinite centralizer rank
  (`unit-roots-divide-centralizer-rank`), none of them conjugate to an infinite-order Thompson unit
  (`thompson-units-have-few-roots-in-leavitt-unit-group`).
- **Power conjugacy.** `BS(1,2) = <[[1,1],[0,1]], diag(2,1)> <= GL_2(Q)`. So some unit is conjugate to its
  square. It then has infinite centralizer rank (`leavitt-heisenberg-centers-have-infinite-centralizer-rank`,
  part iii) and zero depth rate (`depth-distortion-obstructs-power-conjugates-in-leavitt-hosts`).
- **n >= 3.** `H_3(Z) <= GL_3(Q)`, so `F_2[H_3(Z)]` must embed in `R`
  (`leavitt-heisenberg-centers-have-infinite-centralizer-rank`, part ii). `SL_3(Z) <= GL_3(Q)` must embed in `U`.
  Whether it does is not recorded in the graph.

## Refuted if

- `leavitt-unit-centralizers-have-finite-rank` holds (route
  `no-rationals-in-leavitt-units-from-finite-centralizer-rank` to `rationals-do-not-embed-in-binary-leavitt-unit-group`).
- `leavitt-units-of-infinite-order-have-linear-depth-growth` holds. It excludes every `BS(1,k)` with `|k| >= 2`,
  and `BS(1,2) <= GL_2(Q) <= GL_n(Q)`.

## Attempts

**Linear over a commutative subalgebra: dead (lane gq-ring-alt, 2026-09-17, not independently reviewed).**
For a commutative ring `A` of prime characteristic `p` and any `m`, no element of infinite order of `GL_m(A)` is
conjugate to its square. So `BS(1,2)`, and with it `GL_n(Q)` for `n >= 2` and `Aff(Q)`, does not embed in any
`GL_m(A)`. In particular the route of `leavitt-subalgebra-linear-groups-satisfy-boone-higman` cannot reach
`GL_n(Q)` through a commutative subalgebra. *Proof.*
- Suppose `c a c^(-1) = a^2` in `GL_m(A)`.
- For a prime `P` of `A`, let `S` be the multiset of eigenvalues of `a` over an algebraic closure of
  `Frac(A/P)`. Then `S = S^2`, so squaring permutes `S` and every `λ in S` has `λ^e = 1` for `e = 2^(m!) − 1`.
- So `a^e − 1` is nilpotent mod `P`, and `a^M = 1` mod `P` for `M = e·p^r` with `p^r >= m`. This `M` is
  independent of `P`.
- Hence the entries of `a^M − 1` lie in the nilradical. They generate a nilpotent ideal `I`, with `I^s = 0`.
- So `(a^M − 1)^s = 0` and `a^(M p^t) = 1` for `p^t >= s`. Thus `a` has finite order, while the base of
  `BS(1,2)` has infinite order. ∎

**Roots by companion matrices: no gain.** Under `R ≅ M_k(R)`, the amplification `a ⊕ ... ⊕ a` has the
`k`-th root given by the companion matrix of `a`. Chaining these into `(Q,+)` requires units conjugate to their
amplifications. That is `leavitt-units-are-not-conjugate-to-diagonal-copies` (OPEN), so this route meets the
same finite-rank question. The same companion roots already exist in `V`, so they bring nothing new.

**Self-similar fixed point: not in `R`.** Consider the equation `a = s_0 t_1 + s_1 a t_0`. It says that `a` is the
image of `[[0,1],[a,0]]` under `R ≅ M_2(R)`, and it forces `a^2 = s_0 a t_0 + s_1 a t_1`, the diagonal copy of `a`.
Iterating gives `a − s_1^J a t_0^J = Σ_(j<J) s_1^j s_0 t_1 t_0^j` for every `J`. For the free-group grading of
`leavitt-free-group-leading-term-forces-linear-depth`, the right side has `J` nonzero homogeneous components of
distinct degrees `x_1^j x_0 x_1^(-1) x_0^(-j)`. The left side has at most twice as many components as `a`. So
no `a in R` solves the equation. Its formal solution is the binary odometer, and the odometer route to `Z[1/2]`
leaves `R`.
