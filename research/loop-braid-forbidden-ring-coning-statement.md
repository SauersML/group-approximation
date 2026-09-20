---
rg: 2
id: loop-braid-forbidden-ring-coning-statement
kind: claim
title: "Coning statement: for free count N ≥ 11, the q∈{0,3} subcomplex Y_n(F;v,w) of the loop braid descending link is ⌊(N−5)/3⌋-connected"
distinct_from:
  loop-braid-descending-links-are-increasingly-connected: that is the target (all of X_n highly connected); this is a stronger-in-one-degree statement about the q in {0,3} subcomplex Y, not implied by the target, which suffices for it via the Morse filtration
artifacts:
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
  - research/artifacts/zp-loop-braid-one-ring-push-absorbed-block-2026-09-17.md
  - experiments/loop-braid-one-ring-push-2026-09-17/absorbed_block_output.txt
  - research/artifacts/zp-loop-braid-isotropy-spectral-sequence-2026-09-17.md
  - experiments/loop-braid-isotropy-2026-09-17/e2_row1.py
  - experiments/loop-braid-isotropy-2026-09-17/e2_Y11_p3.txt
  - experiments/loop-braid-isotropy-2026-09-17/e2_validation.txt
  - experiments/loop-braid-isotropy-2026-09-17/e2_Y12_p3.txt
  - experiments/loop-braid-isotropy-2026-09-17/om_homology.py
  - experiments/loop-braid-isotropy-2026-09-17/om_homology_output.txt
  - research/artifacts/zp-loop-braid-one-ring-push-fox-coloring-obstruction-2026-09-19.md
---

Notation is from the artifact §0–§1.
- `X_n = L_n(LB_*)`, with `P = PLB_n` acting on it with strict fundamental domain `Q ≅ OM(K_n)`.
- `t: X_n → Q` is the type retraction.
- For `F ⊂ [n]`, `X_n(F) = t^{-1}(OM(K_{[n]∖F}))`, with free count `N = n − |F|`.
- For distinct free rings `v, w`, `Y_n(F; v, w)` is the full subcomplex of `X_n(F)` on the
  vertices whose type pair meets `{v, w}` in `∅` or in `{v, w}`.

**Claim.** For every `N ≥ 11`, and all `n, F, v, w` with free count N, `Y_n(F; v, w)` is
`η(N) = ⌊(N − 5)/3⌋`-connected.

Only the degree `j = η(N)` for `N ≡ 0, 2 (mod 3)` is new content. Lower degrees follow from the
induction (artifact §4.4).

Equivalently, at that degree: every j-sphere in `X_n(F ∪ {v, w})` dies after coning off the links
of the vertices of type `(v, w)` and `(w, v)` (artifact §5.1).

The claim is **not** implied by the target `loop-braid-descending-links-are-increasingly-connected`,
because `(X_n(F), Y)` is only `η(N)`-connected. It is therefore a genuine intermediate statement.

Structure (artifact §5.2):
- Y has strict fundamental domain `Σ OM(K_{N−2})`.
- Y is covered by the stars of its type-`{v, w}` vertices, so the Björner nerve criterion reduces
  the claim to connectivity of `lk(b_0) ∩ … ∩ lk(b_t)`.
- Cable-twist orbits (annuli) can be collapsed.

Evidence (artifact §6):
- the degree-1 strengthening fails at N = 7, where `H_1` of the stabilizer colimit over `Q_Y` has
  extra 3-torsion;
- degree 1 passes the `H_1` test at N = 8, 9.

## Attempts

- 2026-09-17 (swarm-0917-w8-w8-z-last1): stated, with its reduction role and structure. The BFMWZ
  Thm 3.10 step (★), "cut along α ∪ α' to get a smaller surface", has no analogue because annulus
  compatibility is a global unlink condition (artifact §7). The open sub-question there,
  one-ring pushes `b' = A_{vc}·b`, is the next step.
- 2026-09-19 (swarm-0917-w17-w17-z-last1): answered the one-ring sub-question (★);
  artifact `zp-loop-braid-one-ring-push-absorbed-block-2026-09-17.md`.
  - **Literal (★) is false (proved).** `A_ca[(a,b)] ∈ lk(b0)` avoids c, but it is not in
    `lk(A_vc b0)`. The certificate is the P-invariant `rank(pC_u ∩ qC_z)` for the free factors
    `C_(a,b) = ⟨x_a x_b, x_k⟩`, computed by Stallings graphs. It separates vertices that no
    abelian invariant can separate.
  - **Absorbed-block embedding (proved).** The rule `A_cj ↦ A_cj A_vj A_wj` gives an injective
    `θ : PLB_{n−2} → P_vw ∩ C(A_vc, A_wc)` and an embedding `X_{n−2}(F ∪ {c}) ↪ lk(b0) ∩ lk(A_vc b0)`,
    with free count N − 3. Recorded as `loop-braid-one-ring-push-link-contains-absorbed-block`.
  - **Equality (★′) is open.** It has 5040/5040 random agreement, and it is reduced to a
    double-coset statement (K) about `P_vw ∩ ker π`, plus a type exclusion (C). Recorded as
    `loop-braid-one-ring-push-link-equals-absorbed-block`.
  - Under (★′), the one-ring pairs meet the t = 1 Björner condition exactly:
    `c(N−3) = η(N) − 1`.
  - **Not closed.** Longer pushes, such as `A_vc A_vd`, absorb bigger blocks and should lose more
    free count. So the plain nerve over all b fails, and a refined nerve is needed.
  - The suggested decomposition (artifact §5) is:
    - (D1) (★′);
    - (D2) a push-length Morse order on the type-{v, w} vertices, in which descending links meet
      only through one-ring pushes;
    - (D3) chains of one-ring pushes give iterated absorbed blocks, losing 3 free count per step.
- 2026-09-19 (swarm-0917-w19-w19-z-last1, family cohomology-index): **refutation test passed, CS
  still open.** Artifact `zp-loop-braid-isotropy-spectral-sequence-2026-09-17.md`.
  - Tool: the P-isotropy spectral sequence of Y. By Jensen–McCammond–Meier together with cabling,
    E^1 is a subspace coefficient system U^q ⊂ H_q(P). Row 0 splits, because the domain is strict.
  - Theorem A: CS at N = 11 forces H_2(Q_Y) = 0 and E^2_{1,1} = H_1(Q_Y; U^1) = 0 over every
    field.
  - A Čech resolution of W/U turns E^2_{1,1} into the cokernel of a finite linear map
    (`e2_row1.py`). In degree 1 the script reproduces the §6 colimit ranks, including the N = 7
    3-torsion anomaly.
  - At N = 11 over F_3, which is the only nonvacuous characteristic, since
    H_1(OM(K_7); Z) = Z/3: the target has dim 288, the rank is 288, and coker = 0. At N = 12 the
    test is vacuous.
  - Consequence: the N = 7 obstruction mechanism does not recur in the first new degree. The
    spectral sequence gives no further information at total degree 2. This family cannot prove CS,
    and a proof needs geometric input (the nerve, or the one-ring push).
- 2026-09-19 (swarm-0917-w14-w14-z-last1): the one-ring push does not give a family member
  (`loop-braid-one-ring-push-mutual-link-is-not-family-member`, artifact
  `zp-loop-braid-one-ring-push-fox-coloring-obstruction-2026-09-19.md`).
  - Write `I = lk(b0) ∩ lk(A_vc^{±1} b0)`.
    - By the clasp homomorphism, I contains no vertex whose type meets c, so `I ⊆ L_c`.
    - But `A_ca[(a,d)] ∈ L_c ∖ I`. The certificate is a Fox 3-coloring
      `ρ = (0,1,2,0,0; 1…)`: the `P_b0`-invariant set `{c_v ≠ c_w}` is separated from the
      `P_(a,d)`-orbit of `ρ·p`, which has `c_v = c_w`.
    - So `I ⊊ L_c`: the natural candidate `I ≅ X_{n−1}(F∪{f,c})` of w8 §7 is dead.
  - The same holds for the w11 §0.5 `A_av` repair.
  - The obstruction is invisible to e and to D4, and appears with S3 and A4 (3-local, like w8 §6).
  - Open: the exact form of I (candidate: the `(P_b0 ∩ P_b')`-orbit of Q avoiding v, w, c) and
    its connectivity.
