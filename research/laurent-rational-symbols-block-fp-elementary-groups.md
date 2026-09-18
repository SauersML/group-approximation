---
rg: 2
id: laurent-rational-symbols-block-fp-elementary-groups
kind: claim
title: Over a skew Laurent ring B[u^±1; σ] whose base detects rational scalars in K_1, the symbols {λ, u} are infinitely generated in K_2, so no E_N is finitely presented
distinct_from:
  rational-scalars-obstruct-fp-elementary-hosts: that excludes hosts in which rational scalars are elementary (K_1 does not detect them); this excludes skew Laurent hosts in which K_1 of the base does detect them, through K_2.
  leavitt-scalar-commutators-block-fp-central-quotients: that is the purely infinite Leavitt mechanism making scalars central and elementary; this is the opposite regime, a crossed product by Z whose scalars survive.
  harmonic-cuntz-simple-group-is-not-finitely-presented: that refutes finite presentation of one purely infinite harmonic host via its central scalars; this refutes it for every crossed product by Z over a scalar-detecting base, including the tracial harmonic ring.
  aperiodic-subshift-ring-unstable-k2-vanishes: that is characteristic 2, where K_1(LC(Y, F_2)) = 0 and the symbols vanish; this is the characteristic-0 case, where they do not.
artifacts:
  - research/artifacts/gq-deep-adelic-1-k-budget.md
---

**ESTABLISHED** by `laurent-rational-symbols-block-fp-elementary-groups-proof` (lane proof, not
independently reviewed). It uses the Ara–Brustenga–Cortiñas fibration
(`abc-twisted-laurent-k-theory-fibration`) and standard facts: Bass–Heller–Swan, Kervaire's
theorem that `K_2(R)` is the centre of `St(R)`, and B. H. Neumann's lemma. Naturality of the
fibration in the pair `(B, σ)` was not re-read at the source.

## Statement

Let `B` be a unital ring with a unital subring `Q ⊆ B`, let `σ` be a ring automorphism of `B`
fixing `Q` pointwise, and let `R = B[u, u^(-1); σ]` (so `u b = σ(b) u`).

Assume the image of `K_1(Q) = Q^x -> K_1(B)` is not finitely generated. This holds, for example,
whenever `B` is commutative, since `det` sends `[λ]` to `λ` and so the image is all of `Q^x`.

1. **Symbols.** `λ` commutes with the unit `u`. The Steinberg symbols `{λ, u} ∈ K_2(R)`,
   `λ ∈ Q^x`, generate a subgroup that maps onto the image of `Q^x` in `K_1(B)`. In particular
   they generate a subgroup that is not finitely generated.
2. **No finitely presented elementary group.** For every `N >= 3`, `E_N(R)` is not finitely
   presented. Nor is `E_N(R)/C` for any finite normal subgroup `C`. In particular, if
   `Z(E_N(R))` is finite, `PE_N(R)` is not finitely presented.

## Consequences

- **The tracial harmonic ring.** For `R_h` of `tracial-harmonic-ring-keeps-rational-scalars`, the
  base `B` is commutative and `Z(E_N(R_h)) ⊆ {±I}`. So `E_N(R_h)` and `PE_N(R_h)` are not
  finitely presented for any `N >= 3`, and `R_h` is not a host for
  `q-algebra-with-fp-simple-projective-elementary-group`.
- **Every crossed product by Z over a commutative Q-algebra.** This covers `LC(X, Q) ⋊ Z`, the
  continuous-function versions, and skew Laurent rings over commutative harmonic or resolvent
  bases.
- **The K-budget, with `rational-scalars-obstruct-fp-elementary-hosts`.**
  - If rational scalars die in `K_1`, `PE_N` is not finitely presented.
  - If they survive in `K_1` of a Laurent base, `K_2` receives them through `{λ, u}`, and `E_N` is
    not finitely presented.
  - A host must detect scalars in `K_1` while the symbols `{λ, x}` stay finitely generated in
    `K_2`. See `research/artifacts/gq-deep-adelic-1-k-budget.md`.

## Attempts

None beyond the proof.
