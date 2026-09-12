---
rg: 2
id: char-p-linear-embedding-projective-leavitt-power-proof
kind: route
title: Realize the localized polynomial ring in L_p^(⊗d), land in E_m by Whitehead, and avoid the scalar centre
target: char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
requires:
  - leavitt-center-is-coefficient-field
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

This is artifact Lemmas A--C and Theorem C.

1. **Reduction to a ring.**
   - The entries of the generators and their inverses generate a field that is
     finite, of degree `e`, over `F_p(t_1, ..., t_d)`.
   - The regular representation, then clearing all denominators into one `h`,
     gives `H <= GL_(ne)(F_p[t_1..t_d][1/h])`.
   - For `d = 0`, a companion matrix puts the finite entry field in
     `M_e(F_p)`.
2. **Lemma A.** `F_p[t_1..t_d][1/h]` embeds unitally in `R_d`. This is Lemma
   7.1 of `boone-higman-leavitt-tensor-hosts-2026-09-12.md` over `F_p`:
   - the Thompson unit `g` has pairwise distinct `g^k(v)` on the test module,
     over any field, so `F_p[g^±] -> L_p` is injective;
   - monic normalization `f = t_d h / c`;
   - `C[t_d][1/f] ≅ C[g^±][T]/(f(T) - g)` is free over `C[g^±]`;
   - induction on `d`, and leaf coordinates `M_k(R_d) ≅ R_d`.
   So `H <= GL_N(R_d)`.
3. **Lemma B (Whitehead).**
   `diag(X, X^-1) = [[I,X],[0,I]][[I,0],[-X^-1,I]][[I,X],[0,I]] ·
   [[I,-I],[0,I]][[I,0],[I,I]][[I,-I],[0,I]]` holds over every ring, with every
   factor elementary. So `diag(X, X^-1, 1, ..., 1) ∈ E_m(R_d)` for `m >= 2N+1`.
4. **Lemma C (centre).** A matrix commuting with every `e_ij(r)` is `cI` with
   `c` central.
   - `Z(R_d) = Z(L_p)^(⊗d) = F_p` by `leavitt-center-is-coefficient-field`.
   - So the centre of `E_m(R_d)` is inside `F_p^x I`.
   - A scalar with last diagonal entry `1` is `I`, so the embedding meets the
     centre trivially.
5. **Simplicity.**
   - `R_(d-1)` is central simple: `L_p` is simple with centre `F_p`, and a
     tensor product of a central simple algebra with a simple algebra over a
     field is simple with the other factor's centre.
   - Part 4 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`
     with `B = R_(d-1)` makes `E_m(R_d)` modulo its scalar centre simple for
     `m >= 3`.
