---
rg: 2
id: discrete-factor-tree-lattices-are-virtually-products
kind: claim
title: A product-of-trees lattice with a discrete factor image is virtually the kernel of that factor times a free group, so three-tree lattices with a discrete factor satisfy permutational Boone--Higman
distinct_from:
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that needs trivial kernels (a faithful or separating set of factors); this needs a discrete factor image and allows every kernel to be nontrivial.
  product-of-trees-lattices-satisfy-permutational-boone-higman: that is the open universal claim; this settles its three-factor case whenever some factor image is discrete, and pins the remaining case down.
---

**ESTABLISHED** through `discrete-factor-tree-lattice-splitting-proof`
(lane proof, elementary; not independently reviewed; no priority claimed).

**Setting.** As in `product-of-trees-lattices-with-faithful-factor-satisfy-pbh`:
`n >= 2`, `X = T_1 x ... x T_n`, `Gamma` acts on `X` with finite vertex
stabilizers and finitely many vertex orbits, `Gamma_0` is the factorwise
subgroup (finite index), `pr_i : Gamma_0 -> Aut(T_i)` has kernel `K_i`, and
`H_i` is the `Gamma_0`-stabilizer of a vertex of `T_i`. Replacing each `T_j` by
the minimal `pr_j(Gamma_0)`-invariant subtree (and dropping finite factors)
changes nothing about `Gamma`, so assume every `T_j` is infinite and minimal,
hence leafless.

**Statement.** Suppose `pr_i(Gamma_0)` is discrete in `Aut(T_i)` for some `i`.
1. `K_i` has finite index in `H_i`. So `K_i` acts on `X_i' = prod_(j != i) T_j`
   factorwise with finite vertex stabilizers and finitely many vertex orbits:
   it is a lattice of the same kind on `n - 1` factors.
2. `Gamma_0` has a finite-index subgroup isomorphic to `K' x F`, where `K'` has
   finite index in `K_i` and `F` is a finitely generated free group (possibly
   trivial).
3. If `K_i` lies in `B_A`, then `Gamma` lies in `B_A`
   (`boone-higman-type-a-class-closed-under-finite-extensions`).

**Three factors.** For `n = 3`, `K_i` is a lattice on two trees, which lies in
`B_A` by `product-of-two-trees-lattices-satisfy-permutational-boone-higman` (or
is virtually `Z^2` if both remaining trees are lines). So **every lattice on a
product of three trees with some discrete factor image lies in `B_A`**, and all
its subgroups embed in finitely presented simple groups.

**What is left for three trees.** Combined with items 3 and 4 of
`product-of-trees-lattices-with-faithful-factor-satisfy-pbh`, a three-tree
lattice outside `B_A`, if one exists, must satisfy, for every `i`:
- `pr_i(Gamma_0)` is non-discrete;
- `K_i` is infinite, since a finite `K_i` acts trivially on `X` (see the route);
- `K_i` is an infinite normal subgroup of infinite index in the two-tree lattice
  `H_i`, so `H_i` fails the normal subgroup property (it is not just-infinite,
  and neither the Burger--Mozes nor the Margulis/Bader--Shalom normal subgroup
  theorem applies to it);
- `QZ(L_i) != 1`, where `L_i` is the closure of the image of `Gamma_0` in
  `prod_(j != i) Aut(T_j)`.

**Scope.** Nothing here decides whether such "totally non-discrete" lattices
with nontrivial kernels exist. For `n >= 4` the reduction in item 3 needs the
`(n - 1)`-factor case for `K_i`.
