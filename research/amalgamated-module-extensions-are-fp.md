---
rg: 2
id: amalgamated-module-extensions-are-fp
kind: claim
title: A split extension S ⋊ W is finitely presented when S ⋊ V is for a subgroup V and each extra generator of W commutes with a subgroup of V whose translates of finitely many elements generate S
distinct_from:
  leavitt-cantor-module-semidirect-product-is-fp: that is the instance with W the binary Leavitt unit group, S = C(C, F_2), V Thompson's group and one transvection; this is the general amalgamation lemma for any S, W and V.
  orbit-finite-quotient-module-extensions-are-fp: that obtains finite presentation from finitely generated stabilizers and finite double cosets, which make W a type (A) actor; this obtains it from a finitely presented sub-extension and commuting covering subgroups, with no stabilizer hypothesis on W.
---

**ESTABLISHED** by `amalgamated-module-extension-fp-proof`. Elementary; no novelty is
claimed. It is the argument of `leavitt-cantor-module-fp-via-thompson-amalgam` with the
Leavitt data removed.

## Statement

Let `W` be a finitely presented group acting on a group `S` by automorphisms, and
`V <= W` a subgroup with `S ⋊ V` finitely presented. Suppose `W = <V, x_1, ..., x_r>` and
that for each `j` there are

- a subgroup `C_j <= V` whose elements commute with `x_j` in `W`, and
- finitely many `m_(j,1), ..., m_(j,n_j) ∈ S` such that the elements `c·m_(j,l)`
  (`c ∈ C_j`, all `l`) generate `S`.

Then `S ⋊ W` is finitely presented.

## Use

With `S = C(C, F_2)` and Thompson's `V` acting by precomposition, `S ⋊ V` is finitely
presented (`cantor-module-thompson-v-product-is-finitely-presented`), and `V` already has
at most three orbits on `S`. So any finitely presented `W` with `V <= W <= Aut(S)` and
covering data as above yields an orbit-finite affine actor `S ⋊ W`; see route
`affine-actors-via-covered-cantor-module-amalgams`.
