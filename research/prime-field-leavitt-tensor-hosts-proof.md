---
rg: 2
id: prime-field-leavitt-tensor-hosts-proof
kind: route
title: Rerun the characteristic-two transfer with odd-p weights, signed transporters and scalar-centre root detection
target: prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
requires:
  - khanh-acyclicity-and-steinberg-criteria
  - leavitt-center-is-coefficient-field
artifacts:
  - research/artifacts/boone-higman-prime-field-leavitt-hosts-2026-09-12.md
  - research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md
  - GroupApproximation/Leavitt/DiagonalNormalExtraction.lean
---

This follows artifact Sections 1--4. The characteristic-two host theorem does
not imply this one, so the route depends only on the general criteria and the
centre calculation. The arguments below repeat the characteristic-free steps
instead of citing that claim.

1. **Characteristic-free steps.** These are the arguments of
   `leavitt-tensor-hosts-khanh-transfer-proof`, which never use `p = 2`:
   - the division lemma over `B ⊗ L_p`, using `Σ y_k c z_k = 1` and same-length
     words;
   - frame extension, and the compression with `w c(u) w^-1 = c(c(u))`;
   - Menal--Moncasi GE, Voronetsky's refinement, Krstić--McCool.
2. **Acyclicity criterion over `F_p`.** Khanh Lemma 2.3 at odd `p`.
   - `H_j` of an elementary abelian `p`-group is killed by `p` in positive
     degrees.
   - `H*(V; F_p) = Λ ⊗ S` has weights that are sums of at most `j` powers
     `p^a`.
   - Carrying `p` counters into the next position shows that no such sum is
     `0` mod `p^m - 1` for `0 < j < m`.
   - The norm kills nontrivial characters, and `p^m - 1` is prime to `p`.

   Lemma 2.4 and Theorem 2.2 then hold verbatim for `F_p`-algebras with
   `A^2 ≅ A`, since `F_(p^m)` embeds in `A` through `A ≅ M_m(A)`.
3. **Steinberg criterion in every characteristic.**
   - Signed transporters `τ'`, `h'` satisfy `τ' h' τ' = h' τ' h'`, and
     `η(k(a,b,H)) = k(-b, a, H)`.
   - Their Weyl lifts `W`, `W_23` act on generators by the signed substitution
     read off from the matrices. For example `W X_1j(c) W^-1 = X_2j(c)` and
     `W X_2j(c) W^-1 = X_1j(-c)`, from the Steinberg relations alone.
   - So `z = (W_23 W W_23)(W W_23 W)^-1` is central, and `ψ(T) = W z` satisfies
     both presentation relations.
4. **Simplicity modulo the centre.** This is a paper argument that reads the
   Lean proof. It is not a Lean theorem, and nothing here is certified by a
   build.
   - `Z(B ⊗ L_p) = F_p` by `leavitt-center-is-coefficient-field`.
   - In `exists_elGen_mem_of_diagonal`, `hcentral` enters only through
     `center_elementaryGroup_eq_bot_of_units`, to make the chosen `g` noncentral.
   - For a normal `N` not inside the scalar centre, choose `g ∈ N` noncentral;
     root detection and strong division give `N = E_n`.
5. **For `p = 2`.** All signs are trivial and `z = 1`. The statement is then the
   two characteristic-two prerequisites.
