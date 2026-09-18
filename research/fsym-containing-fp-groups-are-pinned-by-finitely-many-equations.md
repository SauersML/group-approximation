---
rg: 2
id: fsym-containing-fp-groups-are-pinned-by-finitely-many-equations
kind: claim
title: A finitely presented permutation group that contains FSym(X) inside a finitely generated subgroup has its remaining generators pinned by finitely many equations, with a Schreier-ball test for non-finite-presentation
distinct_from:
  free-shift-houghton-like-envelopes-are-not-fp: that proves the Houghton-like envelopes H_n(E_nu(P)) of free-shift enumerations are not finitely presented, and its item 3 is the finite-determination statement for those envelopes and enumerations; this is the same mechanism stated for an arbitrary subgroup of Sym(X) containing FSym(X), together with a local criterion (Schreier balls) that turns "finitely many equations do not pin the generators" into a checkable condition.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general finite-presentation criterion for quotients; this is a rigidity property of finitely presented groups acting on X that contain every finitary permutation.
---

**ESTABLISHED** (lane proof, elementary, written inline; not independently reviewed; no priority claimed — the
mechanism is folklore-level, and main already uses it for `free-shift-houghton-like-envelopes-are-not-fp`).

**Setting.** `X` is an infinite set, `E <= Sym(X)` contains `FSym(X)`, and `S = A ⊔ B` is a finite generating set
of `E` such that `H = <A>` already contains `FSym(X)`. For a tuple `T` of permutations of `X`, `Sch(T)` is the
Schreier graph of `<T>` on `X` with edges `x -> t x` labelled by `t in T`. A *relation of `S` of length `<= L`* is
a word of length `<= L` in `S^{±1}` that is trivial in `E`.

**Statement.**
1. **Rigidity.** Every homomorphism `phi : E -> Sym(X)` with `phi(a) = a` for all `a in A` is the inclusion.
2. **Pinning.** If `E` is finitely presented, there is `L` such that `B' = B` is the only tuple
   `B' in Sym(X)^B` for which every relation of `S` of length `<= L` still holds when each `b in B` is read as `b'`.
3. **Ball test.** Let `S' = A ⊔ B'` with `B' in Sym(X)^B`. If every rooted labelled `L`-ball of `Sch(S')` is
   isomorphic, as a rooted labelled graph, to some rooted labelled `L`-ball of `Sch(S)`, then every relation of `S`
   of length `<= L` holds for `S'`.
4. **Non-finite-presentation criterion.** If for every `L` some `B' ≠ B` satisfies the hypothesis of 3, then `E`
   is not finitely presented.

**Proof.**
1. `phi` fixes `H = <A>` pointwise, hence fixes `FSym(X) <= H`. For `e in E` and `f in FSym(X)`, `efe^-1` lies in
   `FSym(X)`, so `efe^-1 = phi(efe^-1) = phi(e) f phi(e)^-1`. Thus `c = e^-1 phi(e)` centralizes `FSym(X)`. For
   `x in X` and any two distinct `y, z ≠ x`, `c` commutes with `(x y)` and `(x z)`, so `c` preserves
   `{x,y} ∩ {x,z} = {x}`. So `c = 1` and `phi(e) = e`.
2. Any finite generating set of a finitely presented group carries a finite presentation. Take one on `S` and let
   `L` be its maximal relator length. If `B'` satisfies all relations of length `<= L`, then `S -> S'` extends to a
   homomorphism `phi : E -> Sym(X)` fixing `A`. By 1, `phi` is the inclusion, so `B' = B`.
3. A word `w` of length `<= L` is trivial as a permutation exactly when, from every root `y`, the path read along
   `w` returns to `y`. That path stays in the `L`-ball of `y` and uses only edges between its vertices. If
   `Psi : B_L^{Sch(S')}(y) -> B_L^{Sch(S)}(x)` is a rooted labelled isomorphism, it carries the `w`-path from `y` to
   the `w`-path from `x`, which is closed because `w` is a relation of `S`. So the path from `y` is closed.
4. By 3, such a `B'` satisfies every relation of length `<= L`. If `E` were finitely presented, 2 would force
   `B' = B` for the `L` given there. ∎

**Use.** Criterion 4 is local: it asks only that a perturbed generator tuple create no Schreier ball that the
original lacks. It applies whenever the generators in `B` carry "generic" data that `A` cannot see. Example
(recovering the mechanism of `free-shift-houghton-like-envelopes-are-not-fp` under a Baire-generic hypothesis):
for `E = H_n(E_nu(P))`, `n >= 2`, take `A` = generators of the Houghton group `H_n` (which contains
`FSym([n] x N)`), let `B` consist of the `rho(g)`-generators on each ray plus finitely many `E_2`-generators, and
conjugate the ray-1 `rho`-generators by a transposition of two far even points. If `nu` contains, beyond every
bound, a right-translated and position-shifted copy of every finite partial prescription `P ⇀ N` — a comeagre set
of `nu`, by the usual open-dense argument — then every ball of the perturbed Schreier graph near the transposition
reappears, shifted by an even translation (under which all `A`- and `E_2`-generators are equivariant far out), in
`Sch(S)`. Criterion 4 then gives non-finite-presentation. The node above proves the stronger statement under the
weaker hypothesis that `P * <s>` embeds as `R_nu`.
