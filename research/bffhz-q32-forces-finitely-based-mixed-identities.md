---
rg: 2
id: bffhz-q32-forces-finitely-based-mixed-identities
kind: claim
title: If the Theorem C action image for a finitely presented simple group S at rank n is finitely presented, then the mixed identities of S in n-1 variables are finitely based over all overgroups of S
distinct_from:
  a2-kernel-removal-forces-recursive-kernel: that derives recursive one-variable mixed identities from removability of the kernel through a sharp embedding; this derives from finite presentation of the image itself a finite set of mixed identities whose satisfaction in any overgroup forces all of them, which implies recursiveness and is a structural rather than computability condition.
  fp-simple-group-with-nonrecursive-mixed-identities: that asks for an undecidable set of mixed identities; this proves that finite presentation of the action image forces a finite basis, a property every group of that claim lacks.
  bffhz-q32-for-fp-simple-groups: that is the open published Question 3.2; this is an established necessary condition for it at one group and one rank.
  bffhz-action-image-is-finitely-presented: that is the refuted universal upgrade to computably presented cores, killed by an MIF core; this concerns non-MIF finitely presented cores, where the kernel is nontrivial.
  thompson-t-mixed-identity-problem-is-decidable: that decides the mixed identities of T; whether they are finitely based over overgroups, as this claim requires of T, is not addressed there.
---

**ESTABLISHED** through `bffhz-q32-finitely-based-mixed-identities-proof`. Not
independently reviewed; no novelty claimed.

## Definitions

Let `S ≤ M` be groups and `k >= 1`. Put

```text
J_k(M; S) = { w in S * F_k : φ(w) = 1 for every homomorphism φ : S * F_k -> M restricting to the inclusion on S } .
```

Then `J_k(S) = J_k(S; S)` is the set of `k`-variable mixed identities of `S`, and
`J_k(M; S) ⊆ J_k(S)`. Say `M` *satisfies* a set `W ⊆ S * F_m` when
`W ⊆ J_m(M; S)`.

`J_k(S)` is **finitely based over overgroups** when there are `m` and a finite
`W ⊆ J_m(S)` such that every group `M ⊇ S` satisfying `W` has
`J_k(M; S) = J_k(S)`.

## Statement

Let `S` be an infinite finitely presented simple group and `n >= 2`. Put
`A = Aut_S(S * F_n)`, `X_M = Hom_S(S * F_n, M)` and `K_M = ker(A ↷ X_M)`, with
`K = K_S`.

**(A) Finite basis from finite presentation.** Suppose `A/K` is finitely
presented, the instance `(S, n)` of BFFHZ Question 3.2. Then there is a finite
`W ⊆ J_n(S)` such that for every group `M ⊇ S` satisfying `W`:
1. `K_M = K`;
2. `J_k(M; S) = J_k(S)` for every `k <= n - 1`.

In particular `J_1(S), ..., J_(n-1)(S)` are finitely based over overgroups.

**(B) Finite basis is a normal-closure presentation.** For any group `S`, finite
`W ⊆ J_m(S)` and `k >= 1`, the following are equivalent:
1. every `M ⊇ S` satisfying `W` has `J_k(M; S) = J_k(S)`;
2. `J_k(S)` is the normal closure in `S * F_k` of the substitution instances
   `w(p_1, ..., p_m)`, for `w in W` and `p_1, ..., p_m in S * F_k`.

**(C) Finite basis implies recursive.** If `S` is finitely presented with solvable
word problem and `J_k(S)` is finitely based over overgroups, then `J_k(S)` is
recursive.

**Contrapositive.** Let `S` be an infinite finitely presented simple group whose
`J_1(S)` is not finitely based over overgroups. Then for every `n >= 2` the
quotient of `Aut_S(S * F_n)` by the kernel of its action on `Hom_S(S * F_n, S)` is
not finitely presented. That answers BFFHZ Question 3.2 negatively for `S`. The
route `q34-from-bffhz-q32-for-fp-simple-groups` then gives nothing for `S`.

## Not claimed

- **No witness.** No finitely presented simple group with non-finitely-based mixed
  identities is exhibited. That is the open claim
  `fp-simple-group-with-non-finitely-based-mixed-identities`.
- **Strictness unknown.** Part (C) makes the finite basis condition at least as
  strong as recursiveness. No recursive but non-finitely-based example is known here.
- **No converse.** A finite basis for `J_(n-1)(S)` is not shown to give finite
  presentation of `A/K`. Part (A) uses only the transvections `x_n -> x_n u` with
  `u` in `J_(n-1)(S)`, while `K` contains other elements.
  - *The free-group analogue.* With no constants and target `Z`, `Aut(F_n)` acts on
    `Hom(F_n, Z) ≅ Z^n` with kernel `IA_n`. The analogues of the transvections of (A)
    are `x_n -> x_n u` with `u` in `[F_(n-1), F_(n-1)]`, the laws of `Z` in `n - 1`
    variables. Their normal closure in `Aut(F_n)` is a proper subgroup of `IA_n`.
  - *The obstruction.* The Johnson homomorphism `τ : IA_n -> Hom(H, Λ^2 H)`, with
    `H = Z^n`, is `Aut(F_n)`-equivariant, and so is the contraction
    `C : Hom(H, Λ^2 H) -> H`. The image of `x_n -> x_n u` is `e_n^* ⊗ ū`, where `ū`
    lies in `Λ^2` of the span of `e_1, ..., e_(n-1)`, so `C` kills it. So `C τ`
    vanishes on the whole normal closure. But the partial conjugation
    `x_1 -> x_2 x_1 x_2^-1` has `τ = ± e_1^* ⊗ (e_1 ∧ e_2)` and `C τ = ± e_2 != 0`.
  - *What this shows.* Kernels of such actions need not be normally generated by pure
    transvections. The analogue is a heuristic, not a statement about simple `S`.
