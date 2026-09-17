---
rg: 2
id: clean-ck-cover-separation-proof
kind: route
title: Compute the elementary image in the sandwich normal form and use it as the separator
target: clean-ck-cover-separates-trivial-words-from-normal-generators
requires: [decidable-fp-group-embeds-in-decidable-derived-subgroup, sandwich-ring-word-problem-reduces-to-its-group, ck-steinberg-marked-cover]
---

**Recursive kernel.** `T` is finitely generated with solvable word problem.
By `sandwich-ring-word-problem-reduces-to-its-group`, equality in
`U = Z[T]<p,q>/(p(1-g)q-1)` is decidable from ring expressions in the
generators of `T`, their inverses, `p` and `q`. So equality of `4 x 4`
matrices over `U` is decidable.

`Gamma` is finitely generated, by `ck-steinberg-marked-cover`: it is a
quotient of the finitely presented `St_4(U)` by finitely many relators.
Each of the finitely many generators maps under `rho` to a fixed matrix in
`EL_4(U) <= GL_4(U)`. Record its entries, and those of its inverse, once as
ring expressions. That is finite data. For a word `w`, multiply the
corresponding matrices symbolically and decide whether the product equals
the identity. So `{w : rho(w) = 1}` is recursive.

**Containment and disjointness.**

- If `w = 1` in `Gamma`, then `rho(w) = 1`.
- Suppose `rho(w) = 1` and `<<w>>_Gamma = Gamma`. Then `Gamma <= ker rho`,
  so `Q` is trivial. But `Q` contains the diagonal copy of `H`, and `H` is
  nontrivial because `g != 1`. This is a contradiction.

So `ker rho` contains `Z_Gamma` and misses `NG_Gamma`.

**Consequences.**

1. The recursive set `ker rho` separates `Z_Gamma` from `NG_Gamma`, which
   gives item 1.
2. Given a poison `(w_n, A, B)`, the set `{n : rho(w_n) = 1}` is recursive,
   because the sequence `w_n` is computable. It contains `A` and misses `B`,
   which contradicts inseparability. This gives item 2.
3. Item 3 is `Q` itself.

**Necessity remark.** Let `M` be maximal with `Gamma/M` recursively
presented. `Gamma/M` is simple and nontrivial, and finitely generated, so its
word problem is decidable. Run two enumerations in parallel:

- the consequences of the relators, which certify `w = 1`;
- the consequences of the relators and `w`, which certify `w != 1` once
  every generator becomes trivial.

This is the two-enumeration argument recorded in
`simple-envelope-forces-solvable-word-problem`. So `M` is recursive.

- `M` contains `Z_Gamma`.
- A word `w in M` with `<<w>> = Gamma` would force `M = Gamma`.

So `M` is a recursive separator. A finitely normally generated `M` makes
`Gamma/M` finitely presented, and in particular recursively presented. `∎`

A runnable check of the normal form, including the relation
`p(1-g)q = 1` acting as the identity and the Z-linear independence of
irreducible words on random inputs over a free group, is
`experiments/ck-clean-cover-poison-2026-09-17/sandwich_normal_form.py`.
