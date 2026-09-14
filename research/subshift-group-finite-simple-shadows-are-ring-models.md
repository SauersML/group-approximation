---
rg: 2
id: subshift-group-finite-simple-shadows-are-ring-models
kind: claim
title: Every sequence of finite simple groups converging to G_X eventually consists of PSL_3d(F_2^f) coming from ring maps of the free algebra
distinct_from:
  simple-lef-groups-are-limits-of-finite-simple-groups: that shows finite simple approximants exist and have unbounded rank; this asks whether their type is forced (projective special linear in characteristic 2, induced by ring maps) for the subshift groups.
  subshift-group-model-sizes-see-rational-spectrum: that settles the sizes for ring-type approximants; this asks whether every approximant is ring type, which would make those sizes, and so the rational spectrum of X, invariants of the abstract group G_X.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part3.md
---

**OPEN.** Let `X` be an infinite minimal subshift and `G_X = EL_3(LC(X,F_2) ⋊ Z)`. Question: if
`(Q_k, T_k) → (G_X, T)` in the space of marked groups with `Q_k` finite simple (for any finite generating set `T`),
are the `Q_k` eventually `PSL_(3d_k)(F_(2^(f_k)))`, with markings induced by ring maps `F → M_(d_k)(F_(2^(f_k)))`?

Consequence of a yes: by `subshift-group-model-sizes-see-rational-spectrum`, the orders of the finite cyclic factors of
`X` would divide the sizes of all finite simple shadows. So the rational spectrum of `X` would be an isomorphism
invariant of `G_X`.

## Attempts

- **Full Steinberg relations suffice (sk-free-4, artifact part 3 §3).** Suppose the approximant satisfies all Steinberg
  relations over the free algebra `F`.
  - The root kernels coincide with a two-sided ideal `I`, and `A = F/I` is finite.
  - `Q_k` is a quotient of `St_3(A)`, which is a central extension of `E_3(A)` (stable rank 1).
  - The congruence kernel to `A/J(A)` is a 2-group, so `Q_k = PSL_(3d)(F_(2^f))`.
- **Where it dies.**
  - Marked convergence gives the Steinberg relations only up to bounded degree.
  - The partial quotient has dimension `≤ log_2|Q_k| = O(N_k^2)`, while `R_X` keeps growing, so no stabilization occurs
    inside the convergence radius.
  - A finite presentation of the Steinberg group over `F` with elementary generators would close the gap, by the
    argument of `kazhdan-marked-limits-eventually-uniform-expanders`. For rank 3 this is doubtful: the analogous groups
    over `F_q[t]` are not finitely presented (Behr; Rehmann–Soulé; recalled, not checked). Rank `≥ 4` is untested.
- **Rank at least four: settled (sk-free-4, artifact part 4).** `el-rank-four-finite-simple-shadows-are-ring-models`:
  - for `N >= 4` and every f.g. ring `R`, every finite simple approximant of `EL_N(R)` is eventually
    `PSL_(Nd)(F_q)`, induced by a surjective ring model;
  - the inputs are the finitely presented `St_N` (Krstić–McCool Theorem 3, via EJZ l.2496–2497, read at source)
    and central `K_2` over finite rings (`semilocal-steinberg-groups-have-central-k2`);
  - consequence: `rank-four-subshift-groups-see-rational-spectrum`.

  The same proof works in rank three EXCEPT step 1: `St_3` over a free ring surjecting onto `F[t]` is not finitely
  presented (Krstić–McCool Corollary 2, quoted by EJZ l.2501). So the question below is exactly whether
  approximants of `G_X` satisfy the Steinberg relations beyond the convergence radius.
- **Settled with a cyclic factor, and the consequence obtained anyway (sk-rank3-shadows, 2026-09-14,
  `research/artifacts/sk-rank3-shadows-2026-09-14.md`; unreviewed).**
  - `cyclic-factor-subshift-groups-have-ring-type-shadows`: if `X` has a finite cyclic factor of order `m ≥ 2`, then
    `G_X = EL_(3m)(R_(X_1))` over the induced subshift, and rank-four type rigidity gives every approximant ring type
    `PSL_(3md)(F_(2^f))`. So this question is OPEN only for totally minimal `X`.
  - `subshift-group-isomorphism-preserves-rational-spectrum`: the intended consequence holds in rank three with no
    answer to this question. For `m ∈ Cyc(Y)`, `m` puts `3m` in `Div(G_Y)` by type rigidity of `EL_(3m)(R_(Y_1))`. If
    `m ∉ Cyc(X)`, periodic models of sizes `g_r p` avoid `3m`. So `G_X ≅ G_Y` forces `Cyc(X) = Cyc(Y)`.
  - Sharpest remaining target (artifact §4): a local-to-global lemma. Ring-type corner subgroups `PSL_(3hd)` over the
    pieces of a clopen partition should force the whole finite simple approximant to be ring type.
- **Remaining rank-three routes.**
  - A finitely presented cover of `EL_3(R_X)` whose finite quotients still carry full root-subgroup structure. EJZ's
    cover (D1 ∪ D2, for algebras over `F_q` with `q >= 5`) has only degree-two commutator relations and does not
    help over `F_2`.
  - Or an intrinsic group-theoretic recovery of the rational spectrum of `X` from `G_X` (see sk-iso-rigidity).
