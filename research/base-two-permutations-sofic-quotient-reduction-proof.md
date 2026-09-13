---
rg: 2
id: base-two-permutations-sofic-quotient-reduction-proof
kind: route
title: Intersect the rotation orbit of the kernel, extend by the rotation, and apply the Kassabov--Kuperberg--Riley equivalence with automatic injectivity
target: base-two-exponential-permutations-iff-sofic-higman-quotient
requires:
  - bs1m-higman-sofic-quotients-iff-exponential-permutations
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**Setup.**
- Let `G = BS(1,2) = < a, b | b^a = b^2 >` and `phi : <b> -> <a>`, `b -> a`.
- Put `P = H_4(G, phi) = < G, t | t^4 = 1, b^t = phi(b) >`.
- By the import `bs1m-higman-sofic-quotients-iff-exponential-permutations`, `P`
  contains `H4 = Hbar_4(G, phi)` as a normal subgroup with `P/H4 = C_4`. Conjugation
  by `t` restricts to an automorphism `tau` of `H4` that permutes the four
  Baumslag--Solitar subgroups cyclically.
- The same import says that item 1 of the target holds exactly when `P` has a
  sofic quotient `Q` in which the natural map `G -> Q` is injective. Call this
  item 3.

**Two permanence facts, proved directly.** Use Helfgott--Juschenko's
definition of an `(S, delta, n)`-approximation (Definition `def:sofic`).
- *Subgroups and finite products.* Restricting an approximation to a subset
  gives an approximation of a subgroup. Given approximations `psi_j` of `S_j` in
  `Sym(n_j)` for `j = 1..r`, the product map on `[n_1] x ... x [n_r]` has
  multiplicativity defect at most `r delta`. For a nontrivial tuple, some
  coordinate `g_j != 1`, so the fixed-point fraction is at most that of
  `psi_j(g_j)`, which is below `delta`.
- *Finite-index overgroups.* Let `Lambda <= Gamma` have index `r` and be sofic.
  Choose coset representatives `t_1..t_r` and write `g t_i = t_(g.i) c(g,i)` with
  `c(g,i)` in `Lambda`. For an approximation `psi` of `Lambda` on a finite set
  containing every needed cocycle value, put
  `Psi(g)(i, x) = (g.i, psi(c(g,i)) x)`. The cocycle identity
  `c(gh, i) = c(g, h.i) c(h, i)` bounds the defect of `Psi` by the defect of
  `psi`. A fixed point `(i, x)` of `Psi(g)` needs `g.i = i`, and then
  `c(g,i) = t_i^-1 g t_i != 1`. So the fixed-point fraction is below `delta`.

**Item 1 => item 2.** Take `Q` from item 3. The image of `H4` in `Q` is a
subgroup of a sofic group, so it is sofic. It contains the injective image of
`G`, so it is nontrivial.

**Item 2 => item 1.** Let `N` be a normal subgroup of `H4` with `N != H4` and
`H4/N` sofic.
- Put `N' = N cap tau(N) cap tau^2(N) cap tau^3(N)`. Since `t^4 = 1`, `N'` is
  `tau`-invariant, and it is normal in `P = H4 <t>`.
- The diagonal map embeds `H4/N'` in `prod_(i=0..3) H4/tau^i(N)`. Each factor is
  isomorphic to `H4/N` through `tau^i`, so `H4/N'` is sofic by the first
  permanence fact.
- `Q = P/N'` contains `H4/N'` with index 4, so it is sofic by the second.
- `N' <= N != H4`, so by `nontrivial-higman-quotients-keep-all-four-bs-subgroups`
  the subgroup `G = <a,b>` meets `N'` trivially. So `G -> Q` is injective.

This is item 3, which gives item 1 by the import. The moduli coprime to `m = 2`
are exactly the odd `n`.
