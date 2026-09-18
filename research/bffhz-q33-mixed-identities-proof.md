---
rg: 2
id: bffhz-q33-mixed-identities-proof
kind: route
title: Proof that BFFHZ Question 3.3 is normal finite generation of mixed identities, descends in rank and forces a finite basis
target: bffhz-q33-is-normal-finite-generation-of-mixed-identities
requires:
  - bffhz-q32-forces-finitely-based-mixed-identities
---

Lane proof, elementary. `G` is finitely presented. Put `H_k = G * F_k`, with free
basis `x_1, ..., x_k` of `F_k`, and `J_k = J_k(G)`.

**Mixed identities are closed under substitution.** Let `w ∈ J_m` and
`p_1, ..., p_m ∈ H_k`. Take a homomorphism `φ : H_k -> G` that is the identity on
`G`. Then `x_i ↦ φ(p_i)` defines a homomorphism `H_m -> G` that is the identity on
`G`. So `φ(w(p_1, ..., p_m)) = w(φ(p_1), ..., φ(p_m)) = 1`. Hence
`w(p_1, ..., p_m) ∈ J_k`. In particular `J_k` is a normal subgroup of `H_k`.

**1.** `H_k` is finitely presented. A quotient of a finitely presented group by a
normal subgroup `N` is finitely presented iff `N` is the normal closure of finitely
many elements. This is the standard fact recorded in the repo as
`fp-quotient-iff-kernel-finitely-normally-generated`.

**2.** Let `j <= k`. Let `ρ : H_k -> H_j` fix `G` and `x_1, ..., x_j` and send
`x_{j+1}, ..., x_k` to `1`. Let `ι : H_j -> H_k` be the inclusion, so `ρ ι = id`.
- `ρ(J_k) ⊆ J_j`. If `w ∈ J_k` and `φ : H_j -> G` fixes `G`, then `φ ρ : H_k -> G`
  fixes `G`, so `φ(ρ(w)) = 1`.
- `J_j ⊆ ρ(J_k)`. We have `ι(J_j) ⊆ J_k`, because every `G`-homomorphism
  `H_k -> G` restricts along `ι` to a `G`-homomorphism `H_j -> G`. So
  `J_j = ρ(ι(J_j)) ⊆ ρ(J_k)`.

So `J_j = ρ(J_k)`. If `J_k` is the normal closure of `w_1, ..., w_r` in `H_k`, then
`ρ(J_k)` is the normal closure of `ρ(w_1), ..., ρ(w_r)` in `H_j`, because `ρ` is
onto. Now apply part 1.

**3.** Suppose `J_j` is the normal closure in `H_j` of `w_1, ..., w_r`; this holds
for every `j <= k` by parts 1 and 2. Take `W = {w_1, ..., w_r} ⊆ J_j` and `m = j`.
- The substitution instances of `W` in `H_j` include the `w_i` themselves: put
  `p_i = x_i`.
- They all lie in `J_j`, by closure under substitution.

So the normal closure of the instances is exactly `J_j`. That is condition B.2 of
`bffhz-q32-forces-finitely-based-mixed-identities`, which is equivalent there to
"finitely based over overgroups". Recursiveness under solvable word problem is part
(C) of the same node.

**4.** Mixed-identity-free means `J_k = 1`, and the quotient is `H_k`, which is
finitely presented. ∎
