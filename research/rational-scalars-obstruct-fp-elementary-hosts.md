---
rg: 2
id: rational-scalars-obstruct-fp-elementary-hosts
kind: claim
title: Over a ring containing Q, elementary rational scalars make PE_N(R) and R^x/Z(R^x) infinitely presented, so K_1 must detect almost all of Q^x
distinct_from:
  rank-four-elementary-center-obstructs-simplicity: that is the central involution -I_4, which obstructs simplicity of EL_4 and is removed by passing to PE_4; this obstructs finite presentation of PE_N itself, through the infinitely generated central group of rational scalars, which passing to the quotient cannot remove.
  projective-elementary-fp-kernel-criterion: that gives the general criterion (finite normal generation of the Steinberg kernel plus a finitely generated centre) for finitely presented R and n >= 4; this computes what the centre clause forces for every ring containing Q and every N >= 3, with no finite presentation of R assumed.
  infinite-field-leavitt-units-are-not-finitely-generated: that shows L_k(1,2)^x and its scalar quotient are not finitely generated over an infinite field; this is ring-general and applies even when R and R^x are finitely generated.
  fg-subrings-of-integral-form-algebras-omit-q: that removes rings with finitely generated structure constants as coefficient rings; this constrains every remaining coefficient ring through K_1.
---

**ESTABLISHED** by `rational-scalars-obstruct-fp-elementary-hosts-proof`
(lane proof, not independently reviewed; no novelty claimed).

## Statement

Let `R` be a nonzero unital ring with a unital map `Q -> R`, and let `N >= 3`.
Put `E = E_N(R)`, `P = PE_N(R) = E/Z(E)`, and
`Λ_N(R) = {λ ∈ Q^x : λ I_N ∈ E_N(R)}`, a subgroup of `Q^x` containing `±1`.

1. **Finite generation.** If `P` is finitely generated, then so are `E` and the
   ring `R`.
2. **Centre clause.** If `P` is finitely presented, then `Z(E)` is finitely
   generated, and so `Λ_N(R)` is finitely generated. In particular `Λ_N(R)`
   involves only finitely many primes. When `P` is simple, every simple quotient of
   `E` is `P` itself, so no other simple quotient of `E_N(R)` can serve as the host.
3. **Elementary scalars kill the host.** If `GL_N(R) = E_N(R)`, or more generally if
   `Λ_N(R)` is not finitely generated, then `PE_N(R)` is **not** finitely presented.
4. **Unit groups.** `Q^x ⊆ Z(R^x)`. If `R^x` is finitely generated, or perfect,
   then `R^x / Z(R^x)` is **not** finitely presented. Also, `R^x` itself is never simple.
5. **A sufficient condition for the centre clause.** If the kernel of the natural
   map `K_1(Q) = Q^x -> K_1(R)` is finitely generated, then `Λ_N(R)` is finitely
   generated.

## Consequences for the root `gl-n-q-embeds-in-fp-simple-group`

- **The characteristic-2 Leavitt tensor template does not transplant to Q.** Over
  `F_2`, `boone-higman-via-central-simple-leavitt-tensor-host` uses
  `R = B ⊗ L` with `K_1(R) = K_2(R) = 0`. Then `R^x = GL_3(R) = E_3(R)` is finitely
  presented and simple (`leavitt-tensor-hosts-acyclic-steinberg-and-fp`,
  `central-simple-leavitt-tensor-unit-groups-are-simple`). Its scalars are
  `F_2^x = 1`.
  - That template obtains `GL_m(R) = E_m(R)` and a perfect `R^x` from `K_1 = K_2 = 0`.
    Any ring `R ⊇ Q` with `GL_N(R) = E_N(R)` for some `N >= 3`, or with `R^x`
    perfect, falls under parts 3 and 4 (the rational scalars are central, and elementary
    when `GL_N = E_N`), so neither
    `PE_N(R)` nor `R^x/Z(R^x)` can be finitely presented.
  - Vanishing `K_1` is exactly the wrong property in characteristic 0.
- **What a ring host must have instead.** A ring `R ⊇ Q` with `PE_N(R)` finitely
  presented needs `Λ_N(R)` finitely generated. That is, `λI_N` must be non-elementary
  for every `λ` outside a finitely generated subgroup of `Q^x`. The natural
  certificate is a `K_1`-type invariant in which `λ^N` survives (part 5), such as a
  determinant or a reduced norm. This holds for commutative rings
  (`det(λI) = λ^N`), but no finitely generated commutative ring contains `Q`. It
  should also hold for the Weyl algebra `A_1(Q)`, where `K_1(Q) -> K_1(A_1(Q))` is an
  isomorphism by Quillen's theorem on filtered rings (cited from memory, not checked
  here). But that ring is not finitely generated
  (`fg-subrings-of-integral-form-algebras-omit-q`).
- **Purely infinite simple coefficient rings.** Ara–Goodearl–Pardo give
  `K_1(R) = U(R)^ab` (`agp-purely-infinite-simple-k1-is-unit-abelianization`). A
  purely infinite simple `R ⊇ Q` passes the test of part 5 only if `U(R)^ab` retains
  the rational scalars up to a finitely generated subgroup. When
  `GL_N(R)/E_N(R) -> K_1(R)` is injective, this is also necessary: the kernel of
  `Q^x -> K_1(R)` then lies in `Λ_N(R)`.
- **Where the obstruction binds.** It bears on
  `q-algebra-with-fp-simple-projective-elementary-group`, and on every
  construction of a finitely generated ring containing `Q` that is aimed at
  `E_N(R)` or `R^x` hosts: operator rings with harmonic or inverse-number
  operators, and `B ⊗ L` with `B ⊇ Q`.
