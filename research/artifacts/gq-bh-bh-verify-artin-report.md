# bh-verify-artin: adversarial check of the Artin-group Boone–Higman claims on main

Lane bh-verify-artin, 2026-09-18. This was prompted by finding F1 of `research/artifacts/gq-bh-bh-lit-survey.md` (d7b638fef). Main marks as ESTABLISHED several Artin families that BFFHZ (arXiv:2503.21882v2, after Corollary B) and survey Remark 5.4 (arXiv:2306.16356v3) list as open.

This is a lane check, not an external review. No MathSciNet search was done. Every step below was re-derived or re-read from the node texts at origin/main aab09af2c. Literature imports were checked against the quotations recorded on the import nodes. I read only one source myself: the arXiv abstract of 2503.21882.

## Summary of verdicts

| Claim | Verdict | What carries it |
|---|---|---|
| `c-tilde-artin-groups-satisfy-permutational-boone-higman` (C̃_n, all n) | **PASS** | BFFHZ Theorem A plus classical embeddings. Independent of linearity. |
| `b-tilde-artin-groups-satisfy-permutational-boone-higman` (B̃_n, n ≥ 3) | **PASS** | BFFHZ Theorem A, the Li–Roushon fibration and elementary group theory. Independent of linearity. |
| `spherical-artin-groups-satisfy-boone-higman` (all spherical types, plain form) | **PASS conditional** | Entirely `polynomial-linear-groups-satisfy-boone-higman` (k = 2, m = 1) and its finite-presentation input. |
| `spherical-artin-groups-satisfy-permutational-boone-higman` | **PASS conditional** | Entirely `char-zero-linear-groups-satisfy-permutational-boone-higman`. |
| `e-type-artin-groups-satisfy-permutational-boone-higman` | **PASS conditional** | Same as the row above. |
| `artin-pbh-reduces-to-odd-component-cliques` and `pbh-class-closed-under-common-retract-amalgams` (hence `even-fc-artin-groups-satisfy-permutational-boone-higman`) | **PASS** (core lemma re-derived) | BFFHZ Theorems C and E. I did not re-read them. |
| `admissibly-oriented-artin-groups-satisfy-boone-higman` | Correctly **OPEN** | Conditional on `bh-embeddability-survives-decidable-edge-hnn`. The amalgam-to-HNN fold was re-checked. |

So main's "Artin" greens split into two kinds.
- **C̃_n, B̃_n and the even-FC family** stand on published theorems (BFFHZ A, C, E; Charney–Crisp; Li–Roushon) plus short arguments that I re-derived. Their novelty question is only whether the literature already records these consequences.
- **The spherical exceptional types, E_6–E_8, F_4, H_3 and H_4**, stand entirely on this repo's characteristic-zero linear theorem. Their status is exactly as strong as `polynomial-linear-groups-satisfy-boone-higman` and `elementary-groups-over-polynomial-s-integers-are-fp`. Lane bh-verify-linear owns that check. Nothing Artin-specific is weak.

## 1. C̃_n

**Chain.**
1. A(C̃_n) ≤ B_(n+2). This is Charney–Crisp, arXiv:math/0408412v1, p. 2, quoted verbatim on the node: "A(Bn) and A(~Cn−1) ... are isomorphic to the subgroups of the braid group A(An) leaving fixed one, respectively two, of the punctures". The embedding is classical; the fixed-two-punctures picture goes back at least to Kent–Peifer and Allcock. The route also re-derives it through Allcock's twice-punctured plane and the Fadell–Neuwirth fibration, and those steps check.
2. B_m ≤ Aut(F_m), by Artin's faithful representation.
3. Aut(F_m) embeds in a finitely presented simple twisted Brin–Thompson group, by BFFHZ Theorem A. The arXiv abstract, read 2026-09-18, says: "each Aut(F_n) satisfies the 'permutational' Boone–Higman conjecture, which means the simple group in question can be taken to be a twisted Brin–Thompson group."

**Check.** Both the plain and the permutational property pass to subgroups trivially, since they are embeddings into one fixed group. So A(C̃_n) lies in the same finitely presented simple group as Aut(F_(n+2)). Zaremsky's Corollary B is not even needed. Case n = 1: A(C̃_1) is free of rank 2. **PASS.**

**Priority.** This is a one-line corollary of BFFHZ Corollary B (braid groups) and a classical embedding. Yet BFFHZ ("remains open for ... the Euclidean Artin groups other than type ~An; in rank 3 it is also known for type ~C2 and ~G2") and survey Remark 5.4 both list C̃_n, n ≥ 3, as open. This looks like an oversight in those two sources' bookkeeping, not a new theorem. It should be worded as "an immediate consequence of BFFHZ Corollary B and Charney–Crisp, not recorded in BFFHZ or the survey". No priority should be claimed, and the node already claims none.

## 2. B̃_n (n ≥ 3)

**Chain.** Step by step (route `b-tilde-artin-pbh-via-free-fibre-kernel-proof`):
1. **W acts freely on M.** For u = x + iy, the argument via W_x (Bourbaki V §3) and Steinberg's stabilizer theorem is correct. A nontrivial fixer forces α(u) = α(x) ∈ Z for some root α. The hyperplanes u_k = c and u_i ± u_j = c, c ∈ Z, are the affine B_n root hyperplanes. I re-checked the reflection s_(e_k, c)(u)_k = 2c − u_k, which uses α^∨ = 2e_k.
2. **The type is B̃_n.** The chamber is u_1 > … > u_n > 0, u_1 + u_2 < 1. Its walls e_1 + e_2, e_1 − e_2, e_2 − e_3, …, e_(n−1) − e_n, e_n give a fork at e_2 − e_3 and a double bond at e_(n−1) − e_n / e_n. This is not the C̃_n arrangement. Translations T = D_n, [W : T] = 2^n·n! and [Z^n : T] = 2 all check.
3. **Changes of space.**
   - exp: M → N is the full Z^n-quotient: u_k ∉ Z ⟺ v_k ≠ 1, and u_i ∓ u_j ∉ Z ⟺ v_i ≠ v_j^(±1).
   - α ↦ (α+1)/(α−1) sends 0 ↦ −1 and inversion to negation, so N ≅ P.
   - P × C^× ≅ Y_(n+1).
   - So A_T = π_1(M/T) is an index-2 subgroup of π_1(N), which embeds in π_1(Y_(n+1)).
4. **The fibration** Y_m → Z_m, imported from Li–Roushon (arXiv:2403.09533v2, Bull. Sci. Math. 206 (2026)). Z_(n+1) is aspherical, because Conf_(n+1)(C) ≅ C × Z_(n+1). The fibre is a connected punctured surface, so the π_1 sequence is exact and π_1(Z_(n+1)) ≅ P_(n+1). Rank r = 2g + p − 1 = 3n·2^(n−1) + 1, which is 37 at n = 3 (re-computed).
5. **Centreless-kernel embedding**, Artin's representation, Aut(F_a) × Aut(F_b) ≤ Aut(F_(a+b)), and Krasner–Kaloujnine with Aut(F_m) ≀ S_k ≤ Aut(F_(mk)). All correct.
6. A(B̃_n) ≤ Aut(F_M), so A(B̃_n) inherits both properties from BFFHZ Theorem A by subgroup closure.

**Not re-proved** (as the node says): local triviality of the Li–Roushon map, which is published; and π_1(M/W) ≅ A(B̃_n), which is Nguyễn / van der Lek (standard for Coxeter groups, with the Tits cone equal to all of R^n for affine types). **PASS.**

**Priority.** The combination is not in BFFHZ or the survey, which list B̃_n as open. The node's novelty search was bounded (arXiv only). The residual-finiteness corollary, A(B̃_n) ≤ Aut(F_M), was not priority-checked; the node says so.

## 3. Spherical types: plain form

**Linearity import.** PASS. Cohen–Wales (math/0010204v2) Theorem 1.2 covers A, D and E over Z[r^(±1), t^(±1)]. The representation is faithful after r ↦ r_0 ∈ (0,1), so it is already faithful before specializing. Crisp's LCM embeddings then handle the other types: B_n and I_2(m) into A-types, F_4 into E_6, H_3 into D_6, H_4 into E_8. The node records that no step uses Digne.

**What carries the claim.** A(E_8) ≤ GL_120(Z[r^(±1), t^(±1)]). Z[r^(±1)] is free of rank 2 over Z[r + r^(−1)], on the basis 1, r, because r² − s r + 1 = 0. So A(E_8) ≤ GL_480(Z[s_1, s_2]). Hence the plain spherical claim needs only `polynomial-linear-groups-satisfy-boone-higman` with m = 1 and k = 2. It does not need the full characteristic-zero reduction node, although the route text cites that node. The polynomial theorem in turn rests on:
- `elementary-groups-over-polynomial-s-integers-are-fp` (E_n(Z[s_1, s_2]) finitely presented for n ≥ 6);
- `affine-extension-of-fp-elementary-group-is-fp`;
- `polynomial-parameter-affine-groups-are-self-similar`;
- Zaremsky, arXiv:2405.09722, Theorem 1.1: finitely presented self-similar groups embed in finitely presented simple groups.

**Sanity checks** (not a review of those nodes):
- **Self-similarity.** The action (v, t) ↦ (A(t)v + b(t), t) on Z_p^n × Z_p^k, with p ∤ m, restricts on each cylinder to (v′, t′) ↦ (A(t_0 + p t′)v′ + b′(t′), t′). Its coefficients stay in Z[1/m], and A(t_0 + p t′) ∈ E_n(R), because substitution is a ring endomorphism. So the action is self-similar and faithful, as that node claims.
- **Finite presentation.** The bound n ≥ k + 4 = 6 is consistent with injective K_2 stability, n ≥ dim + 3 with Krull dimension 3. K_2(Z[s_1, s_2]) = K_2(Z) by homotopy invariance. Krstić–McCool's non-finite-presentability of SL_3(Z[t]) is not contradicted, since n is large here.
- I found no problem.

**Verdict.** PASS conditional on the polynomial theorem. The claim is new relative to the literature if and only if that theorem is: bh-lit found the literature reaching only finitely generated subgroups of GL_n(Q). If `polynomial-linear-groups-satisfy-boone-higman` holds, the exceptional spherical types really are settled here, answering a case BFFHZ and survey Remark 5.4 list as open. That makes the polynomial theorem the single highest-value external-verification target among the Artin claims.

## 4. Spherical types: permutational form, and the E types

`spherical-artin-pbh-via-char-zero-linear-groups` and `e-type-artin-pbh-via-spherical-permutational-form` are one-line compositions and check. Everything rests on `char-zero-linear-groups-satisfy-permutational-boone-higman`.

**Status inconsistency.** That node's status line says "Not independently reviewed". Yet `research/artifacts/review-pbh-charzero-spherical-2026-09-13.md` gives it PASS (row 1), and the E-type node cites that same review as "independent review PASS". One of the two lines is stale. As far as I can tell, it is the "Not independently reviewed" line on the characteristic-zero PBH node, which its owner should update. Either way, both reviews are internal to this repo.

## 5. Even-FC and the clique reduction

**Core lemma.** I re-derived `pbh-class-closed-under-common-retract-amalgams`, Part 1, Steps 0–4:
- G = (L * M) ⋊ C by the normal form theorem.
- The fibre product D embeds in a finitely presented simple MIF group H, by BFFHZ Theorem C, (i) ⟹ (iv).
- ρ_a and γ_c are automorphisms of H * F(x, y) fixing H, and (GP1) checks on x, y and H.
- The semidirect relation checks on generators, using (F).
- w is injective, since no two H-letters or y-letters are adjacent.
- Φ is injective, since c commutes with y in a free product only if c = 1.
- G ≤ Aut_H(H * F_2), which carries a type (A) action by BFFHZ Theorem E.
- Steps 5–6 (trees, equivariant graph products) are routine inductions and check.

**Reduction.** The retraction lemma checks: even boundary edges map to u^k = u^k. So do the pushout splitting, the induction on odd components, and the even-FC consequence. For even labels, the irreducible spherical cliques have rank at most 2, so D(Δ) is a matching whose factors lie in B_A (dihedral groups by BFFHZ Corollary B, C̃_2 by §1).

**Verdict.** PASS, modulo BFFHZ Theorems C and E. The recorded quotations match the statements used; I did not re-read them.

**Priority.** Bounded (the artifact's §8). The node's own caveat is right: if even-FC Artin groups were known to be linear in characteristic zero, the FC part would follow from §3.

## 6. Admissibly oriented

Correctly OPEN. It is conditional on the HNN permanence node. The amalgam-to-HNN fold (a ↦ a, b ↦ t^(−1) b t) is well defined and injective by Britton's lemma. That was re-checked.

## Honest status notes landed with this report

A one-paragraph "Verification (bh-verify-artin, 2026-09-18)" note is appended to each checked claim. It states the verdict and exactly which dependency carries the claim. No mathematics was changed.
