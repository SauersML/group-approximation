---
rg: 2
id: singer-identities-make-subshift-el3-isos-standard
kind: claim
title: If an isomorphism G_X → G_Y sends each constant Singer cycle c_V to an element satisfying x³+x = S_V, and the constant Frobenius group has no fixed vectors, then the isomorphism is standard and X, Y are strongly orbit equivalent
distinct_from:
  frobenius-support-idempotents-give-boolean-realization: that assumes the ring identities (O) and (O′) and stops at a Boolean algebra centralizing α(L_X); this derives (O) from the Singer identities and goes on to root subgroups and standardness
  diagonal-recognition-makes-subshift-el3-isos-standard: that assumes α(L_X) is G_Y-conjugate to GL_3(B) with B maximal commutative; this produces the conjugate from the Singer identities and replaces maximality by generation
  subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer: that is the open recognition statement; this is a sufficient condition for it, stated as polynomial identities for images of elements of order 7
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part1.md
---

Let `X, Y` be infinite minimal subshifts, `G_X = EL_3(LC(X,F_2) ⋊ Z)` and likewise `G_Y`, and let `α: G_X → G_Y` be an
isomorphism. Let `c ∈ GL_3(F_2)` be a Singer cycle with `c³+c+I = 0`, `F21 = ⟨c,s⟩` its Frobenius normalizer, `c_V` and
`F21_V` the copies constant on a clopen `V`, and `S_V = I + Σ_{k∈α(F21_V)} k`. Assume:
- **(Sing)** `α(c_V)³ + α(c_V) = S_V` for every clopen `V`;
- **(O′)** `S_X = I`.

Then:
- `S_VS_W = 0` for disjoint `V, W`;
- `α(GL_3(LC(X,F_2))) = k·GL_3(𝔅′)·k^{-1}` for some `k ∈ GL_3(R_Y)` and a Boolean subalgebra `𝔅′ ≅ LC(X,F_2)`;
- `inn(k^{-1})∘α` maps every root subgroup onto the corresponding root subgroup, and equals `M_3(φ)|_{G_X}` for a
  ring isomorphism `φ: R_X → R_Y`.

So `α` is standard, `R_X ≅ R_Y`, and `X` and `Y` are strongly orbit equivalent.

Status: proved in `singer-identities-make-subshift-el3-isos-standard-proof`; PASS-WITH-FIXES by sk-verify-25a and,
independently, by sk-verify-25b, with the fixes merged (sk-rigidity-merge, 2026-09-14). The proof imports:
- the index kernel theorem `subshift-gl3-index-kernel-is-elementary-group` (sk-verify-18 part6 PASS);
- a division step for clopen classes in `K^0(Y,T)`, which is Lemma 2.5 of H. Matui, arXiv:math/0404224, quoted in the
  artifact and read at source by both reviewers (e-print l.272–283).

After Fix A2, Step 5 uses no first-return corner isomorphism. After Fix W3, Step 7 produces the ring isomorphism `φ`
directly, so `peirce-root-homomorphisms-of-e3-are-standard` is no longer needed (it gives the same with `a_ij = E_ij`).

Model tests: the identity and `inn(diag(u,1,1))` satisfy (Sing) and (O′). The graph automorphism has type `3*` and
fails (Sing), so the theorem applies after composing with it. The natural ⊕ trivial fake fails (O′). The Steinberg
fake fails (Sing).

## Review
- **sk-verify-25b PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-25b-2026-09-14.md` §2):** adversarial re-derivation of Lemma 0, Lemma I and Steps 1–7.
  - Computed on MSI: Ext¹_{F_2GL_3(2)}(3,3) = 0 (dim Z¹ = dim B¹ = 8); sl_3 ≅ 8 is irreducible; 8|_{F21} = 2⊕3⊕3*; 3⊗3|_{F21} = 3⊕3*⊕3*; span_{F_2}F21 = M_3(F_2).
  - (Div) read at source: Matui, arXiv:math/0404224 e-print l.272–283, Lemma 2.5, verbatim as quoted.
  - All imports reviewed: index kernel theorem (sk-verify-18 PASS), Proposition F (sk-verify-19), bicommutant closedness (sk-verify-5), Peirce roots (sk-verify-15), matrix ring ⇒ SOE (sk-verify-3), DP (sk-verify-16), K_0 (sk-verify-3, group level).
  - A1: the status line should call the index kernel theorem reviewed.
  - A2: Step 5 needs no Proposition F item 2, and so no corner isomorphism. With (O) and (O′), `S_{X∖V} = I − S_V`. `α(Q_V)` commutes with `K_{X∖V}`, and the kernel of its action on `Fix(K_V)` is normal in the simple `α(Q_V) ≅ GL_3(2)` and contains `K_V`. So `α(q_V) − I = S_V(α(q_V) − I)S_V`.
  - A3: Step 2 should note that restriction to `F21_X` is semisimple (21 odd), so forbidden constituents are summands of `M`.
- **sk-verify-25a PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-25a-2026-09-14.md` §4), independent of sk-verify-25b.** Lemma 0 and Steps 1–7 were re-derived by hand.
  - A separate one-shot MSI script found: `|Z¹| = |B¹| = 256` for `Ext¹(3,3)`; `sl_3` irreducible; `8|_{F21} = 2⊕3⊕3*`; `3⊗3|_{F21} = 3⊕3*⊕3*`; 0 invariant complements of Λ in Sym; span of F21 = `M_3(F_2)`.
  - Matui Lemma 2.5 was checked separately at source, including the numbering: the shared `thm` counter gives df 2.1–2.4, then lem 2.5.
  - Fixes:
    - W2: the Step 6 bicommutant of `A_ij ∩ L_X` is justified by `C_{G_X}(A_ij ∩ L_X) = C_{G_X}(A_ij(R_X))`, since `g_ii = g_jj ∈ D_X` is an invertible idempotent, hence 1. Then item 2 of `el3-root-subgroups-are-bicommutant-closed` applies. "Theorem R Step 3" is not needed.
    - W3: Step 7 gives a ring isomorphism `φ: R_X → R_Y` directly. `φ_ij(1) = 1` and the commutator relations force all `φ_ij` equal, and `α′ = M_3(φ)|_{G_X}`. So `G_X ≅ G_Y ⇒ R_X ≅ R_Y`, and SOE follows with m = 1.
    - W5: Proposition F items 1–2 of the normalizer artifact are the node's item 3.
  - No FAIL, no GAP.
- **Fixes merged (sk-rigidity-merge, 2026-09-14, `research/artifacts/sk-rigidity-merge-2026-09-14.md`):** A1 and W1 (this status line), A2, A3, W2, W3 and W5 into the artifact part 1 §3 and the route.
