---
rg: 2
id: miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel-proof
kind: route
title: Glue Miller's group to an infinite-order core element inside the normal closure, then run CK Theorem 3 on s
target: miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel
requires: [miller-fp-group-with-hereditarily-unsolvable-quotients, chatterji-kassabov-normal-generator-embedding, simple-envelope-forces-solvable-word-problem, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - experiments/ck-miller-poison-2026-09-17/kmss-miller-quote.txt
---

**Setup.**
- Fix `S`, `t in S` of infinite order, and `1 != s in S`, as in the target.
- Let `M` be the finitely presented group of
  `miller-fp-group-with-hereditarily-unsolvable-quotients`.
- `M != 1`, so pick `1 != a in M`.
- Put `B = M * <z>` (free product with an infinite cyclic group) and
  `w = a z a z^-1`.

**Step 1. `w` has infinite order and lies in `<<M>>_B`.**

Membership: `w = a · (z a z^-1)` is a product of two conjugates of elements
of `M`.

Order: for `k >= 1`, `w^k` is the concatenation of `k` copies of the sequence
`(a, z, a, z^-1)`. Each term is a nontrivial element of one free factor, and
consecutive terms lie in different factors. This includes the junction
`z^-1 | a`. So `w^k` is a reduced alternating product of length `4k`, and it
is `!= 1` by the normal form theorem for free products (Lyndon--Schupp,
*Combinatorial Group Theory*, Ch. IV, §1). The same holds for `w^-k`.

**Step 2. The amalgam `G`, and why both factors embed.**

Let

    G = S *_(t = w) B,

amalgamating the infinite cyclic subgroups `<t> <= S` and `<w> <= B` by
`t -> w`.
- *Finitely generated:* generators of `S`, generators of `M`, and `z`.
- *Recursively presented:* take the recursively enumerable relators of `S`,
  the finitely many relators of `M`, and the single relator identifying a
  word for `t` with a word for `w`.

*Both factors embed.* This elementary argument avoids the amalgam normal form.
- Let `W` be `S` or `B`, with `u = t` or `u = w` respectively. `W` is
  countable, being finitely generated.
- Let `W` act on `Omega = W x N` by left multiplication in the first
  coordinate. The action is faithful and free.
- The `<u>`-orbits are the sets `<u>x x {n}`. Each is infinite because `u` has
  infinite order, and there are countably infinitely many of them.
- Enumerate the orbits as `O_0, O_1, ...` and choose base points `p_j in O_j`.
  Sending `u^k p_j -> (k, j)` is a well-defined bijection `Omega -> Z x N`,
  because the action is free.
- It carries `u` to the shift `sigma(k, j) = (k+1, j)`.

Transport both actions to `Z x N`. This gives faithful homomorphisms
`phi_S : S -> Sym(Z x N)` and `phi_B : B -> Sym(Z x N)` with
`phi_S(t) = sigma = phi_B(w)`. By the universal property of the amalgam there
is a homomorphism `Phi : G -> Sym(Z x N)` that restricts to `phi_S` and
`phi_B`. So `S -> G` and `B -> G` are injective. In particular `M <= G` and
`1 != s in G`.

**Step 3. `S <= <<M>>_G`.**

By Step 1, `t = w in <<M>>_G`. `<<t>>_S` is a nontrivial normal subgroup of the
simple group `S`, so it equals `S`. Hence `S = <<t>>_S <= <<M>>_G`.

**Step 4. The envelope.**

`G` is finitely generated and recursively presented, and `s != 1` in `G`.
Apply `chatterji-kassabov-normal-generator-embedding` to `(G, s)`. This gives
`G <= Gamma` with `Gamma` finitely presented, of property (T), and
`Gamma = <<s>>_Gamma`. So `Gamma` contains `S` and meets every hypothesis of
the hole.

**Step 5. Every nontrivial quotient of `Gamma` is undecidable.**

Let `N <| Gamma` with `N != Gamma`.
1. `s notin N`. Otherwise `Gamma = <<s>>_Gamma <= N`.
2. `M` is not contained in `N`. Otherwise `N` contains `<<M>>_Gamma`, which
   contains `<<M>>_G`. By Step 3 that contains `s`, contradicting (1).
3. So the image of `M` in `Gamma/N` is `M/(M ∩ N)`, a nontrivial quotient of
   `M`. By the imported theorem it has unsolvable word problem.
4. A solvable word problem passes to finitely generated subgroups. Write each
   generator of the subgroup once as a fixed word in the generators of the
   ambient group; triviality of a subgroup word is then triviality of its
   translation. Solvability does not depend on the finite generating set.
   So `Gamma/N`, being finitely generated, has unsolvable word problem.

Fix a finite generating set `X` of `Gamma`. The word problem of `Gamma/N` in
the images of `X` is exactly membership in the set of `X`-words representing
elements of `N`. So that set is non-recursive for every proper `N`, including
`N = 1`: `Gamma` itself has unsolvable word problem. This proves (1) of the
target.

**Step 6. No finitely normally generated maximal kernel.**

Suppose `Mx <| Gamma` is maximal proper and finitely normally generated.
- By `fp-quotient-iff-kernel-finitely-normally-generated`, `Gamma/Mx` is
  finitely presented.
- By maximality it is simple, since normal subgroups of `Gamma/Mx` correspond
  to normal subgroups of `Gamma` containing `Mx`. It is nontrivial because
  `Mx` is proper.
- `simple-envelope-forces-solvable-word-problem` (Kuznetsov), applied to the
  finitely generated subgroup `Gamma/Mx` of the finitely presented simple
  group `Gamma/Mx`, gives it solvable word problem.

This contradicts Step 5. So no maximal proper normal subgroup of `Gamma` is
finitely normally generated. Equivalently, `Gamma` has no finitely presented
simple quotient.

More strongly, no maximal kernel is even recursively enumerable. If `Mx` were
r.e., then `Gamma/Mx` would be recursively presented. A finitely generated
recursively presented simple group has solvable word problem by the same
two-enumeration argument. This contradicts Step 5. ∎

## Remarks

- *Orders.* Nothing about torsion in `M` is needed. The infinite-order element
  `w` is manufactured inside `<<M>>_B`, and the core only has to supply `t`.
  If `S` is a torsion group, this construction gives nothing.
- *Steinberg form.* The same `G` can be fed to `ck-steinberg-marked-cover`
  through any finitely presented `H >= G`, which exists by Higman's embedding
  theorem. Step 5 goes through verbatim, because `G <= H <= Gamma` and
  `Gamma = <<s>>_Gamma`. This is recorded only as a remark, since Higman's
  theorem is not imported here. Such an `H` has unsolvable word problem, so
  the marking is not clean.
