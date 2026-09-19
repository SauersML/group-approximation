---
rg: 2
id: three-tree-lattices-escape-only-via-discrete-normal-subgroups
kind: claim
title: A three-tree lattice outside the type (A) class is irreducible and has an infinitely generated normal subgroup acting on a single factor, whose image is a nontrivial discrete normal subgroup of that factor's closure
distinct_from:
  irreducible-tree-lattices-with-jnc-closures-are-pbh: that needs every factor closure just-non-compact and uses Bader--Shalom; this needs no normal subgroup theorem and only excludes discrete normal subgroups of the closures, which is weaker than just-non-compactness.
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: its item 4 asks for trivial quasi-centre of the closure in a product of the other factors; this asks it of the closure in a single tree, where Burger--Mozes theory applies.
---

**ESTABLISHED** through `three-tree-lattice-kernel-commutation-proof` (lane
proof, elementary; not independently reviewed; no priority claimed).

**Setting.** `Γ <= Aut(X)` is a cocompact lattice on `X = T_1 x T_2 x T_3`, each
`T_i` locally finite, leafless and with more than two ends; `Γ_0` preserves the
factors, `K_i` is the kernel on `T_i`, `N_ij = K_i ∩ K_j`, and `Ḡ_k` is the
closure of `pr_k(Γ_0)` in `Aut(T_k)`.

**Statement.** Suppose `Γ` is not in `B_A`. Then:
1. `Γ` is irreducible (no factor or pair of factors has discrete image), and no
   `K_i` is trivial;
2. some `N_ij` (`{i, j, k} = {1, 2, 3}`) is nontrivial. It acts only on `T_k`,
   with finite vertex stabilizers, minimally, and not cocompactly. It is not
   finitely generated;
3. `pr_k(N_ij)` is a nontrivial discrete normal subgroup of `Ḡ_k`, so it lies in
   the quasi-centre `QZ(Ḡ_k)`, and `Ḡ_k` is not just-non-compact.

**Criterion.** So a three-tree lattice lies in `B_A` whenever no factor closure
`Ḡ_k` has a nontrivial discrete normal subgroup, for instance when every
`QZ(Ḡ_k)` is trivial. By `burger-mozes-infinitely-transitive-tree-groups`
item 3, this holds when every non-discrete `Ḡ_k` is locally `∞`-transitive.
Then some factor is faithful, and every subgroup of `Γ` embeds in a finitely
presented simple group.

**Scope.** Residual finiteness is never used. For `n >= 4` factors, the same
commutation argument shows that kernels of adjacent `(n - 2)`-subsets cannot
both be nontrivial, but it does not force a faithful factor (a product of two
irreducible two-tree lattices has nontrivial kernels on complementary pairs).
