---
rg: 2
id: persistent-hosts-build-the-input-from-its-carries
kind: claim
title: In a self-similar group with a persistent retraction onto H and kernel K, the centralizer of K in H embeds virtually in K^X and the rest of H acts on K, so finite-rank carries never reach an input with an infinite-rank abelian subgroup
distinct_from:
  rigid-affine-hosts-are-linear-over-number-fields: that is the barrier for the affine digit hosts R^n ⋊ Q over rigid rings; this holds for every self-similar group with a persistent retraction, affine or not, and bounds the input by its carry kernel.
  linear-groups-over-q-are-quasi-retracts-of-simple-groups: that is LISW Theorem 1.4, whose carry kernel Z[1/N]^n ⋊ ⟨N⟩ has finite rank; this shows why any carry kernel of that kind stops at inputs whose abelian subgroups have finite rank.
---

**ESTABLISHED** by `persistent-hosts-build-the-input-from-its-carries-proof` (lane proof, elementary,
not reviewed). No priority is claimed.

## Setting

- `X` is a finite alphabet and `Γ ≤ Aut(T_X)` is self-similar: `g^x ∈ Γ` for all `g ∈ Γ`, `x ∈ X`.
- A retraction `r: Γ → H` onto a subgroup `H ≤ Γ` is *persistent* if `r(g^x) = r(g)` for all `g`
  and `x` (LISW `def:persistent-retracts`, arXiv:2510.01952v1 l.623).
- `K = ker r`, so `Γ = K ⋊ H`. Call `K` the *carry kernel*: for `h ∈ H`, every state `h^x` lies in
  `K h`.

LISW `lem:pers-retr-implies-quasi-retr` (l.635) turns such a `Γ` into a Röver–Nekrashevych group
that quasi-retracts onto `H`. Their Theorem 1.4 uses `K = K_{n,N} = Z[1/N]^n ⋊ ⟨N⟩`.

## Statement

Let `C = C_H(K)`, and let `C_1 = {c ∈ C : c(x) = x for all x ∈ X}`. So `C_1` has index at most `|X|!`
in `C`.

1. **Carry embedding.** For `c ∈ C_1` put `κ_x(c) = c^x c^{-1}`. Then `κ_x(c) ∈ K`, and
   `κ = (κ_x)_{x∈X}: C_1 → K^X` is an injective homomorphism.
2. **The rest acts on the carries.** Conjugation gives an injective homomorphism `H/C ↪ Aut(K)`.

**Corollary (finite-rank carries).** Suppose `K` has a characteristic subgroup `M` such that:
- `M` is torsion-free abelian of finite rank;
- `K/M` is free abelian of finite rank.

Examples: torsion-free abelian `K` of finite rank (`M = K`), and LISW's `K_{n,N}`, where
`M = Z[1/N]^n` is the unique maximal abelian normal subgroup and `K/M ≅ Z`. Then every abelian subgroup
of the finitely generated group `H` has finite torsion-free rank. So `H` contains no free abelian
group of infinite rank.

**For LISW Question 1.10.** Two targets are excluded from every persistent self-similar host with
such a carry kernel, for every alphabet and every self-similar structure:
- `Z wr Z ≤ GL_2(C)` (`non-fp2-groups-are-quasi-retracts-of-simple-groups`);
- the finitely presented metabelian group `Z[t^{±1},(1+t)^{-1}] ⋊ Z^2`, recorded as open in
  `fg-complex-linear-groups-are-quasi-retracts-of-simple-groups`.

A persistent host for them needs a carry kernel `K` with two properties:
- `K^X` or `Aut(K)` contains an infinite-rank abelian group;
- `K` still has the finiteness of the target.

By Kropholler's theorem (a soluble group of type `FP_∞` is constructible, hence of finite Prüfer rank),
soluble carries of type `FP_∞` are of finite rank. Whether they then satisfy the Corollary's hypothesis
is not checked here.

## Lesson for general BH

- **Coarse control costs carry complexity.** A persistent retraction is what gives a
  Röver–Nekrashevych host a quasi-retraction onto its input. By part 1, it also forces the part of the
  input that commutes with the carries into a finite power of the carry kernel. The rest of the input
  must act faithfully on the carry kernel.
- **The machinery creates no complexity.** In a persistent host, the self-similar construction cannot
  manufacture complexity that is not already present in `K` or `Aut(K)`.
- **What non-persistent hosts buy.** The BH hosts for linear groups on main (parameter coordinates)
  escape because they are not persistent: carries there are absorbed by substitutions. Undistorted or
  quasi-retracting BH hosts for wild inputs must therefore either use carry kernels that already
  contain the wildness, or get the quasi-retraction from a cocycle other than a persistent label.
