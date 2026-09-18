---
rg: 2
id: q-difference-lamplighter-satisfies-boone-higman
kind: claim
title: The q-difference lamplighter Z[1/q][x^±1] ⋊ <x·, f(x) ↦ f(qx)> embeds in a finitely presented simple group
distinct_from:
  q-difference-lamplighter-is-not-quasi-linear: that proves the group is linear over no finite product of fields; this asks for a Boone--Higman envelope that must therefore come from a non-linear host.
  fp-metabelian-groups-satisfy-boone-higman: that settles metabelian groups, including the index-free subgroup K_0 below; this is its mapping torus under the q-difference substitution, of derived length 3.
  fg-soluble-minimax-groups-satisfy-boone-higman: that is the finite-rank soluble class, residually finite or not; this group is residually finite but of infinite rank, and is not quasi-linear.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**OPEN.** Let `q >= 2` and let `K_q = V ⋊ ⟨X, T⟩` be as in
`q-difference-lamplighter-is-not-quasi-linear`. Then `K_q` embeds in a finitely
presented simple group.

## Why it is a sharp test case

- It is finitely generated, residually finite, abelian-by-`H_3(Z)`, and has solvable word
  problem. So it is an instance of the Boone--Higman conjecture that passes every
  residual-finiteness and composition-factor gate on main.
- It is linear over no finite product of fields
  (`q-difference-lamplighter-is-not-quasi-linear`). So the quasi-linear route to `B_A`
  (`quasi-linear-groups-satisfy-permutational-boone-higman`) cannot reach it. It is not
  metabelian. For `q = 2` it is not residually nilpotent either: `[T,X]` acts as `2`, so
  `[[T,X], v] = v` and `V ⊆ ∩_n γ_n(K_2)`. Hence `K_2` is not a subgroup of a free soluble
  group, since those are residually nilpotent (Gruenberg; not read here). So the
  free-soluble route does not reach it.

## A reduction (lane proof, elementary)

`K_q = K_0 ⋊_T Z`, where `K_0 = V ⋊ ⟨X, [X,T]⟩ = Z[1/q][x^±1] ⋊ ⟨x, q⟩` is metabelian,
and therefore in `B_A` (`fp-metabelian-groups-satisfy-boone-higman`).

**Actor lemma.** Let `Γ ≤ Sym(S)` act with type (A)
(`type-a-action-gives-boone-higman-for-subgroups`), and let `π ∈ Sym(S)` normalize `Γ`.
Then `⟨Γ, π⟩` acts on `S` with type (A).
- It is faithful.
- It is finitely presented, as a finite extension or a mapping torus of `Γ`.
- A point stabilizer is an extension of a subgroup of `⟨π⟩Γ/Γ` (cyclic) by `Stab_Γ(s)`,
  hence finitely generated.
- Its orbits on two-element subsets are unions of `Γ`-orbits, so there are finitely many.

So `K_q ∈ B_A` whenever `K_0` sits in a type (A) actor `Γ ≤ Sym(S)` and the substitution
`T` is induced by conjugation by a permutation of `S` that normalizes `Γ`.

## What the standard hosts give (lane remarks)

The metabelian and linear routes on main pass through affine groups `P^N ⋊ E_N(P)` over
polynomial rings `P = Z[1/m][s_1..s_k]`, made self-similar by evaluating parameters. Any
affine parameter map `s ↦ As + b` with `b ∈ Z[1/m]^k` and `A ∈ GL_k(Z[1/m])` of
`ℓ`-adic unit determinant, where `ℓ ∤ m` is the tree prime, is state-closed. Its sections
are again of this form. So the route would close if some embedding `ρ: K_0 → P^N ⋊ E_N(P)`
intertwined `T` with such a map, up to conjugation.
- **Restriction of scalars fails.** Let `R ≅ P^r` and let `T` act through a ring
  automorphism `τ` of `P` entrywise. Then `T X T^-1 = qX` gives `τ(N(x)) = q^r N(x)`,
  where `N(x)` is the norm of `x`. But `τ` fixes `P^× = Z[1/m]^×`, so `q^r = 1`, which is
  false.
- **Laurent parameters fail.** Their units can move, but they lose state-closedness. The
  sections of `s ↦ qs` on `Z_ℓ^×` need the localizations `Z[1/m][s'][(s_0 + ℓs')^-1]` for
  every residue `s_0`.
- **Open.** It is not known whether some other embedding of `K_0` is compatible with an
  affine parameter map, or whether a non-affine host is needed.
