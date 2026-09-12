---
rg: 2
id: a2-kernel-removal-recursive-kernel-proof
kind: route
title: Semi-decide stabilizer membership from both sides, pass the kernel through a finitely presented image, and encode mixed identities as transvections
target: a2-kernel-removal-forces-recursive-kernel
requires:
  - simple-envelope-forces-solvable-word-problem
  - relative-automorphism-action-is-highly-transitive
  - boone-higman-implies-relative-permutational-bh
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**(a)** `G` is finitely presented, so the set of words equal to `1` in `G` is r.e.
There are finitely many orbits on `S x S`, hence on the diagonal, so `S` has
finitely many orbits with representatives `s_1, ..., s_r`.

Let `H_j = Stab(s_j)`, finitely generated. The `G`-orbits of pairs in the orbit
of `s_j` correspond to the double cosets `H_j \ G / H_j`, so there are finitely
many. Choose representatives `d_(j,1) = 1, d_(j,2), ..., d_(j,m_j)`.

For a word `g`, both of the following are r.e.:
- `g in H_j`: enumerate words in the generators of `H_j` and consequences of the
  relators of `G`;
- `g in H_j d_(j,i) H_j` for some `i >= 2`: enumerate the same way.

Exactly one holds, so membership in `H_j` is decidable.

Code points as pairs `(j, g)` standing for `g s_j`. Then `g s_j = g' s_(j')`
exactly when `j = j'` and `g'^-1 g in H_j`, which is decidable, and the action is
computable. Finally, `g` is not in `K` iff `g x s_j != x s_j` for some `j` and
some word `x`, which is r.e.

**(b)** Let `ι : G -> G'` be injective with `ι(G) ∩ K' = ι(K)`. Then `ι` induces
an embedding `G/K -> G'/K'`. `G'/K'` is finitely presented: take a finite
presentation of `G'` and add finitely many normal generators of `K'`. So the
words trivial in `G/K` are r.e.: enumerate consequences of that presentation
applied to `ι` of the generators of `G`. That set is `K`. By (a), `K` is also
co-r.e., so it is recursive.

**(c)** Recall the setting of FFWZ's proof of Theorem 5.1, verified against the
arXiv:2603.24687v2 text:
- `A` is finitely presented, by BFFHZ Proposition 1.1, because `Γ` is finitely
  presented with trivial center;
- the action is highly transitive, with finitely generated point stabilizers
  (`relative-automorphism-action-is-highly-transitive`);
- so the action is of type `[A_2]` (the actor of
  `boone-higman-implies-relative-permutational-bh`).

`Γ` has solvable word problem by `simple-envelope-forces-solvable-word-problem`.
So `J_1(Γ)` is co-r.e.: `w` is not in it iff `w(g) != 1` for some `g`.

*The encoding.* For a letter `a in {c^(±1), y^(±1)}`, with `c` a generator of
`Γ`, let `r_a in A` fix `Γ` and `x_2, ..., x_n` and send `x_1` to `x_1 a'`. Here
`a' = c^(±1)` or `x_2^(±1)`. Since `a'` does not involve `x_1`,

```text
(r_(a_1) ∘ ... ∘ r_(a_k))(x_1) = x_1 a'_1 ... a'_k .
```

Fix once and for all words for the finitely many `r_a` in a finite generating
set of `A`. Then `w = a_1 ... a_k` maps computably to a word for
`α_w = r_(a_1) ∘ ... ∘ r_(a_k)`, which sends `x_1` to `x_1 w(x_2)`.

*The reduction.* `α_w in K` iff `ρ(x_1) ρ(w(x_2)) = ρ(x_1)` for all `ρ in X`.
Equivalently, `w(ρ(x_2)) = 1` for all `ρ`. As `ρ` ranges over `X ≅ Γ^n`,
`ρ(x_2)` ranges over `Γ`, so `α_w in K` iff `w in J_1(Γ)`.

*Consequences.*
- If `J_1(Γ)` is not recursive, neither is `K`.
- Were `A/K` recursively presented on the images of the generators of `A`, `K`
  would be r.e. It is co-r.e. by (a), so it would be recursive. Hence `A/K` is
  not recursively presented, and in particular not finitely presented.
- By (b), no sharp embedding into a type `[A_2]` pair with finitely normally
  generated kernel exists. `∎`
