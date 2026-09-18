---
rg: 2
id: leavitt-scalar-commutators-block-fp-central-quotients
kind: claim
title: A group whose commutator subgroup meets its centre in a non-finitely-generated subgroup has no finitely presented central quotient; so no unit group of a ring with an infinite central field and a Leavitt family is finitely presented modulo its scalars
distinct_from:
  rational-scalars-obstruct-fp-elementary-hosts: that treats PE_N(R) through the elementary scalars Λ_N(R) and R^x/Z(R^x) when R^x is finitely generated or perfect; this needs neither hypothesis and applies to every intermediate group H with L_K(1,d)^x ≤ H ≤ R^x, in particular to the derived unit group [R^x, R^x], and to every central quotient, not only the full centre.
  leavitt-unit-groups-over-every-field-are-simple-mod-scalars: that proves L_k(1,2)^x/k^x simple; this shows that for infinite k it and every overgroup quotient by central scalars fail finite presentation.
  infinite-field-leavitt-units-are-not-finitely-generated: that shows L_k(1,2)^x/k^x is not finitely generated; this reaches every ring containing the Leavitt algebra, including finitely presented rings such as the Leavitt resolvent ring, whose unit groups may be finitely generated.
---

**ESTABLISHED** by `leavitt-scalar-commutators-block-fp-central-quotients-proof`
(lane proof, elementary, no novelty claimed; referee PASS from `gq-referee-a`,
proof-gap lens, report 58d536cf7, and from `gq-referee-b`, citation lens,
`research/artifacts/gq-referee-b-leavitt-scalar-commutators-block-fp-central-quotients.md`,
c81257d90). The `E_N(R)` sentence of part 2 rests on
`leavitt-gl-equals-el-and-perfect-unit-group`, a repository-internal Lean node the
referees did not check; parts 0, 1 and the other instances do not use it.

**Statement.**
0. **Group lemma.** Let `H` be a group, and `C_0 ≤ Z(H) ∩ [H,H]` a subgroup that is
   not finitely generated. Then for every subgroup `C` with `C_0 ≤ C ≤ Z(H)`, the
   group `H/C` is not finitely presented. In particular `H/Z(H)` is not finitely
   presented.
1. **Leavitt families.** Let `R` be a unital ring, `K ⊆ Z(R)` an infinite subfield
   and `d >= 2`. Let `s_1, ..., s_d, t_1, ..., t_d ∈ R` satisfy `t_i s_j = δ_ij` and
   `Σ_i s_i t_i = 1`. The `K`-subalgebra they generate is a copy of `L_K(1,d)`. Put
   `U_d = L_K(1,d)^x ≤ R^x` and `C_0 = {λ^(d-1)·1 : λ ∈ K^x}`, so `C_0 = K^x` for
   `d = 2`. Then for every group `H` with `U_d ≤ H ≤ R^x`, and every `C` with
   `C_0 ≤ C ≤ Z(H)`, the group `H/C` is not finitely presented.
2. **Instances.** Under the hypotheses of part 1, none of the following is finitely
   presented:
   - `R^x / Z(R^x)`;
   - `[R^x, R^x]` modulo its centre, when `d = 2`;
   - `H/Z(H)` for any subgroup `H ≥ L_K(1,d)^x`.

   This holds whether or not `R`, `R^x` or `H` is finitely generated or finitely
   presented. For `d = 2`, `GL_N(L_K(1,2)) = EL_N(L_K(1,2)) ≤ E_N(R)` also gives
   that `E_N(R)` modulo its centre is not finitely presented for any `N >= 2`.

## Consequences for `gl-n-q-embeds-in-fp-simple-group`

- **The Leavitt resolvent route fails at finite presentation.** The ring `R_L` of
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero` contains `Q` centrally and a
  Leavitt `(1,2)` family. So `D/Z(D)`, for `D = [R_L^x, R_L^x]`, is not finitely
  presented. This is `leavitt-resolvent-derived-units-mod-centre-not-fp`. It
  refutes `leavitt-resolvent-derived-units-mod-centre-fp-simple`, so the route
  `gl-n-q-bh-via-leavitt-resolvent-units` is dead. The same holds for
  `R_L^x/Z(R_L^x)` and for `E_N(R_L)` modulo its centre.
- **The obstruction is structural, not a feature of R_L.** It applies to every ring
  that is a `Q`-algebra and has a Leavitt family of any type `(1,d)`. That covers
  `L_Q(1,d)`, `B ⊗ L_Q(1,d)`, Leavitt–Nekrashevych completions over `Q`-algebras,
  corners and matrix rings of these, and any ring containing them. The rational
  scalars, or their `(d-1)`-th powers, are central, are commutators inside the
  Leavitt unit group, and are not finitely generated. No quotient by central
  scalars can be finitely presented.
- **What a Leavitt-type host in characteristic zero must avoid.** A finitely
  presented nonabelian simple group built from such a ring has to be a subquotient
  `H/M` with one of two features:
  - `H` does not contain a full Leavitt unit group `L_Q(1,d)^x`;
  - `M` is not central.

  A central `M` with `H/M` simple and nonabelian must equal `Z(H)`, since `Z(H)/M`
  is central in `H/M`. Then `M ⊇ C_0`, and part 1 applies.

  Passing to a corner does not escape. If `e ~ 1`, then `eRe` is again such a
  ring, with the transported Leavitt family and central `Qe`. So the corner group
  `{u + (1 - e)}` modulo its centre is not finitely presented either.
