---
rg: 2
id: fournier-facio-compression-tree-lamp-group
kind: claim
title: Both compressors turn the simple factor into a binary-tree lamp group inside Gamma
distinct_from:
  fournier-facio-group-contains-simple-wreath-shift: That iterates one compressor and finds a Z-indexed chain of commuting copies; this uses both compressors and the commuting pair P_1 x P_2 to find copies indexed by the whole rooted binary tree, all inside Gamma.
  conjugate-commuting-perfect-copies-force-exponential-dimension: That bounds exact representations containing commuting conjugate perfect copies; this supplies, inside the Kazhdan subgroup of the Fournier--Facio group, 2^n such copies at depth n.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED.**  In the notation of `fournier-facio-torsion-free-skeleton`,
put `alpha_i = Ad(t_i)` for `i = 1,2`, `t_w = t_(w_1) ... t_(w_n)` for a word
`w in {1,2}^*`, and

```text
S_w = t_w pi(S) t_w^-1                 (w in {1,2}^*),   S_(empty) = pi(S).
```

Then:

```text
(TL1)  alpha_1(Gamma) and alpha_2(Gamma) commute with each other and with pi(S);
(TL2)  S_w <= alpha_(w_1)(Gamma) <= Gamma          for every nonempty w;
(TL3)  S_w and S_v commute for w != v;
(TL4)  the multiplication map (+)_(w in {1,2}^*) S_w -> Gamma is injective;
(TL5)  alpha_i(S_w) = S_(iw);
(TL6)  t_1^-1 pi(S) t_1 and t_2^-1 pi(S) t_2 both centralize Gamma;
(TL7)  pi(S) is a direct factor of pi(S) alpha_1(Gamma) alpha_2(Gamma),
       and alpha_1(Gamma) cap alpha_2(Gamma) is central in both.
```

If `S` is not Kazhdan, for example a Burger--Mozes lattice, which acts on a
tree without a fixed point, then `pi(S) alpha_1(Gamma) alpha_2(Gamma)` is a
proper subgroup of `Gamma`.

**Regular models.**  If `u:G -> U(M)` has `tau(u(g)) = 0` for `g != 1`, then
`u((+)_w S_w)''` is the tensor product of copies of the II_1 factor `L(S)`
indexed by the rooted binary tree, and `Ad u(t_i)` maps the slot of `w` onto
the slot of `iw`.

**Consequence for a tensor ansatz.**  `S_2` commutes with every `J_k`, `k in Z`,
from `fournier-facio-group-contains-simple-wreath-shift`, since those are
`S_(1^(k-1))` for `k >= 1`, and the rest centralize `Gamma`.  So a model
whose slots are indexed by `Z` has no slot for `S_2`.  The slot geometry of
any model, face (S1) included, is the rooted binary tree together with the
parent slots of (TL6).  Both compressors act as the two prefix maps, not as
one bilateral shift.

Proof: `fournier-facio-compression-tree-lamp-proof`.
