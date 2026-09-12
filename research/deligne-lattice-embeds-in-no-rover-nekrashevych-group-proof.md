---
rg: 2
id: deligne-lattice-embeds-in-no-rover-nekrashevych-group-proof
kind: route
title: A central infinite cyclic kernel over a finitely presented matrix group decides the word problem, and property (T) blocks every Rover--Nekrashevych embedding
target: deligne-lattice-embeds-in-no-rover-nekrashevych-group
requires:
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf
---

Write `E = Gamma~` and `Q = Sp_4(Z)`, and let `z` generate the central kernel
`Z` of `E -> Q`. Everything used about them is in
`deligne-universal-cover-lattice-is-non-rf-kazhdan`.

## 1. Finite presentation

- Let `Q = <s_1,...,s_k | r_1,...,r_l>` be a finite presentation. It exists because
  `Q` is an arithmetic lattice.
- Choose lifts `t_i` of the `s_i` in `E`. Each `r_j(t)` maps to `1` in `Q`, so
  `r_j(t) = z^(c_j)` in `E` for some integer `c_j`.
- Let `E'` be the group with generators `t_1,...,t_k,z` and relators
  `[t_i,z]` and `r_j(t) z^(-c_j)`. There is a natural map `E' -> E`.
- **The map is onto.** The `t_i` generate `E` modulo the kernel, and the kernel
  is `<z>`.
- **The kernel of the map lies in `<z>`.** In `E'` the element `z` is central
  and `E'/<z>` is `Q`. The map induces the identity of `Q`, so its kernel lies
  in `<z>`.
- **The map is injective.** It sends `<z>` onto the infinite cyclic group `<z>`
  in `E`, so it is injective on `<z>`.

Hence `E' -> E` is an isomorphism, and `E` is finitely presented.

## 2. Solvable word problem

Given a word `w` in `t_1,...,t_k,z`:

- Map it to `Q` by multiplying the fixed integer matrices `s_i`. If the product
  is not the identity, then `w != 1`.
- Otherwise `w` lies in the kernel. So `w = z^c` in `E` for exactly one integer
  `c`, since `z` has infinite order.
- Enumerate the consequences of the finite presentation of step 1 until a
  relation `w = z^c` appears. This search terminates.
- Answer `w = 1` exactly when `c = 0`.

The algorithm depends on the finitely many constants `c_j` and on a word for
`z`. Only their existence is needed.

## 3. No Rover--Nekrashevych embedding

- Suppose `E` embeds in some `V_d(H)` or `V_(d,r)(H)` with `H <= Aut(T_d)`
  self-similar.
- `E` has property (T). By
  `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`, `E` is then
  residually finite. That contradicts Deligne's theorem.
- The same holds for every subgroup of `V_d(H)`, including
  `[V_d(H),V_d(H)]`.

## 4. Refutation

`E` is finitely generated with solvable word problem, and it embeds in no
`[V_d(H),V_d(H)]`. So `decidable-groups-embed-in-rover-nekrashevych-hosts`
fails for the input `G = E`. The route
`boone-higman-via-rover-nekrashevych-hosts` requires exactly that claim, so it
is invalidated.
