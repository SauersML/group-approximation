# Referee report (gq-referee-a, proof-gap lens): central scalar commutators block finite presentation

**Reviewed.** Both nodes were read on origin/main (lane gq-ring-leavitt, 90ff0b8ea):
- `leavitt-scalar-commutators-block-fp-central-quotients` and its route `-proof`;
- `leavitt-resolvent-derived-units-mod-centre-not-fp` and its route `-proof`.

**Verdict: PASS for both.** The refutation of `leavitt-resolvent-derived-units-mod-centre-fp-simple`
is correct. So the route `gl-n-q-bh-via-leavitt-resolvent-units` is dead, as the nodes state.

## 1. The group lemma (part 0)

- **(i) The commutator subgroup lies in `H_0`.** `H/C` is finitely generated, so `H = H_0 C` with
  `H_0` finitely generated. Since `C` is central, `[h_1c_1, h_2c_2] = [h_1,h_2]`. Hence
  `[H,H] = [H_0,H_0] ≤ H_0`, and `C_0 ≤ H_0 ∩ C`. Correct.
- **(ii) The central kernel is finitely generated.** `H_0/(H_0∩C) ≅ H/C` is finitely presented, so
  the kernel of `F → H_0/(H_0∩C)` is the normal closure of finitely many `r_i`. That holds for any
  finite generating set. This kernel is the full preimage of `H_0 ∩ C`, so it maps onto `H_0 ∩ C`.
  The images of the `r_i` are central in `H_0`, so their normal closure is the subgroup they
  generate. Hence `H_0 ∩ C` is finitely generated abelian. Correct: this is the standard Schur-type
  argument.
- **Contradiction.** `C_0 ≤ H_0 ∩ C` would be finitely generated.

## 2. Leavitt families (part 1)

- **The embedding.** The unital map `L_K(1,d) → R` exists because `K` is central. It is injective
  because `L_K(1,d)` is simple and `R ≠ 0`.
- **(iii) The `K_1` step for `d ≥ 3`.** For the rose with `d` petals, Ara–Brustenga–Cortiñas give
  `0 → coker(K_1K →^{1-d} K_1K) → K_1(L) → ker(K_0K →^{1-d} K_0K) → 0`. The right-hand term is
  `ker(Z →^{1-d} Z) = 0`, so `K_1(L) = K^x/(K^x)^{d-1}` through the natural map `λ ↦ [λ·1]`. So
  `[λ^{d-1}·1] = 1`.
  - The Ara–Goodearl–Pardo isomorphism `K_1(L) ≅ U(L)^ab` is induced by `U = GL_1 → K_1`, so it is
    compatible with this map.
  - Hence `λ^{d-1}·1 ∈ [U_d,U_d]`. Correct in logic. Exact theorem numbers are in the citation lens.
- **For `d = 2`.** `U_2` is perfect, which is the recorded node. So `C_0 = K^x·1` directly.
- **`C_0` is not finitely generated.** An infinite field has a multiplicative group that is not
  finitely generated. `λ ↦ λ^{d-1}` has finite kernel. Correct.

## 3. Instances and the `R_L` consequence

- **`[R^x,R^x]` for `d = 2`.** `U_2 = [U_2,U_2] ≤ [R^x,R^x]`, so the scalars lie in `[H,H]` for
  `H = [R^x,R^x]`, and they are central there.
- **`E_N(R)`.** `M_N(L_K(1,2)) ≅ L_K(1,2)` makes `GL_N(L_K(1,2)) = EL_N(L_K(1,2)) ≅ L^x` perfect,
  using the cited GL = EL node. Scalar matrices `λI_N` are central in `GL_N(R)` and are commutators
  inside `EL_N(L) ≤ E_N(R)`. Correct.
- **`R_L`.** `Q ⊆ Z(R_L)`, and `(s_i, t_i)` is a Leavitt `(1,2)` family, so `Q^x ≤ L_Q(1,2)^x ≤ D`
  and `Q^x ≤ Z(D)`. Therefore `D/C` is not finitely presented for `Q^x ≤ C ≤ Z(D)`, and the OPEN claim
  (that `D/Z(D)` is finitely presented and simple) is false.

## 4. Remarks

- **The consequence for hosts is correctly limited.** A finitely presented simple subquotient `H/M` of
  such unit groups needs `M` non-central, or `H` avoiding a full copy of `L_Q(1,d)^x`.
- **The corner argument.** `e ~ 1` gives `eRe ≅ R`-type data, and the obstruction carries over.
  It is stated, not proved in detail. It is plausible and not load-bearing.
- **This does not touch the Steinberg route to Problem 2.7.** `St_m(R_L)` is finitely presented by
  Krstić–McCool. Only its quotients by central subgroups containing the scalar image are blocked, and
  `St_m` itself is not simple anyway.
