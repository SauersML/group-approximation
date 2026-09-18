---
rg: 2
id: fg-complex-linear-groups-are-quasi-retracts-of-simple-groups
kind: claim
title: Every finitely generated subgroup of GL_n(C) is a subgroup and a quasi-retract of a simple group with the same finiteness properties
distinct_from:
  linear-groups-over-q-are-quasi-retracts-of-simple-groups: that is LISW Theorem 1.4 for subgroups of GL_n(Q) (literature import); this is their Question 1.10, the same statement over C.
  fg-linear-groups-embed-in-fp-self-similar-groups: that gives a finitely presented self-similar host with no control of finiteness properties or coarse geometry; this asks for a simple host with the same finiteness properties and a quasi-retract.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN.** Printed as Question 1.10 of Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1
(TeX label `quest:linear-groups-as-retracts`, l.289–297):

> Let H be a finitely generated subgroup of GL_n(C) for some n ∈ N. Does there exist
> a simple group G that has the following properties? (1) G has the same finiteness
> properties as H, (2) H is a subgroup of G, (3) G admits a quasi-retract onto H.

The authors add: "an answer to this question will likely require completely new
techniques" (l.299).

**Lead on main (lane remark, not a proof).** `fg-linear-groups-embed-in-fp-self-similar-groups`
puts `H` in a finitely presented self-similar affine group over
`Z[1/m][s_1,…,s_k]`, whose Röver–Nekrashevych commutator subgroup is finitely
presented and simple (Zaremsky, arXiv:2405.09722, Theorem 1.1). What is missing is
(1) matching finiteness properties below type `F_2` and above it, and (3) a
quasi-retract: the transcendental coordinates `s_j` enter the host, and LISW's
Theorem 1.4 construction retracts only onto the split extension of `H` over `Q`.

## Attempts

1. **LISW's route with transcendental parameters (2026-09-18, lane bh-openq-papers).** Read
   against LISW §§5–7 (TeX l.635–866). Their proof has three steps:
   - (i) `Q ≤ GL_n(R)` for a *rigid* subring `R ⊆ Z_p`, meaning `R ∩ pZ_p = pR`
     (Definition `def:p-rigid`). This makes `R^n ⋊ Q` self-similar with persistent
     retraction onto `Q` (Lemma `lem:rigid-self-similar-and-retract`).
   - (ii) A finiteness step: `Γ = K_{n,N} ⋊ Q`, where `K_{n,N} = ⟨Z[1/N]^n, diag(N)⟩ ≅ Z^n *_{×N}`
     is of type `F_∞`.
   - (iii) The persistent retraction gives a quasi-retraction `V_d(Γ) → Q`
     (Lemma `lem:pers-retr-implies-quasi-retr`).

   **Step (i) extends to `C` (lane proof, elementary).**
   - Choose algebraically independent `τ^(1), …, τ^(k) ∈ Z_p`, and let `τ^(j)_i` be the `i`-fold
     digit shift, defined by `τ^(j)_i = a^(j)_i + p τ^(j)_(i+1)` with digits `a^(j)_i`.
   - Let `R = ⋃_i Z[1/N][τ^(1)_i, …, τ^(k)_i]`, an ascending union of polynomial rings.
   - *`R` is rigid.* If `x = f(τ_i) ∈ pZ_p`, then substituting `τ_i = a_i + pτ_(i+1)` gives
     `x = f(a_i) + p·g(τ_(i+1))` with `g` over `Z[1/N]`. Here `f(a_i) ∈ pZ_p ∩ Z[1/N] = pZ[1/N]`,
     so `x ∈ pR`.
   - Every finitely generated `H ≤ GL_n(C)` embeds in `GL_M(Z[1/N][s_1..s_k])`
     (`char-zero-linear-groups-embed-in-polynomial-s-integer-groups`), hence in `GL_M(R)` via
     `s_j ↦ τ^(j)_0`.
   - So `R^M ⋊ H` is self-similar on the `p^M`-regular tree with a persistent retraction onto `H`.

   **Step (ii) is where it fails.**
   - The translation module must be `H`-invariant and closed under the state maps
     `b ↦ (Ax + b − x')/p`. Once `H` has transcendental entries this forces infinite rank: the
     degree in `τ` grows under the `H`-action.
   - So no analogue of the rank-`n` solenoid `Z[1/N]^n` with one dilation is available. The
     split extension can stay finitely generated, but it typically loses finiteness properties:
     compare `Z[t] ⋊ ⟨t⟩ = Z ≀ Z`, which is not finitely presented, and LISW Remark
     `rem:loosing-Fn`. Condition (1) of the question then fails.
   - A proof along these lines needs a finitely generated, finiteness-preserving substitute for
     `K_{n,N}` that is invariant under both the digit shift of `τ` and the `H`-action. None
     is known.
