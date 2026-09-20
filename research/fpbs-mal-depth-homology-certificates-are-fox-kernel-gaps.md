---
rg: 2
id: fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps
kind: claim
title: At every depth j the best first-homology lower bound for deep_j(Q) is the Fox-kernel difference k_{u_{j+1}}(Q) - k_{u_j}(Q), which is at most the depth-0 certificate k_u of the transported level Q^(j), so homological proofs of Q_j > 0 die at the same Lück approximation question as at depth 0
distinct_from:
  fpbs-mal-modp-promotion-certificates-are-fox-annihilators: that is the depth-0 case (Q_0 = relC(R_L; R_K)), and it leaves deep-label arguments at depth j >= 1 untouched; this computes the homological certificate for deep_j at every depth j >= 1 and reduces it to that depth-0 element through the chain rule u_{j+1} = phi^j(u_1) u_j.
  fpbs-mal-overfold-merges-never-help: that is the open statement deep_j = law_j; this gives an unconditional lower bound deep_j >= k_{u_{j+1}} - k_{u_j}, proves deep_j = law_j on every level where the bound equals law_j, and shows the bound is O(1)-sized on random levels, so it cannot give the weak form deep_j >= c law_j on towers.
  fpbs-mal-depth-promotion-equals-overfold-merge-number: that identifies Q_j with the merge number deep_j; this bounds that merge number from below by homology.
artifacts:
  - research/fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps-proof.md
  - experiments/fpbs-transitive-retract-2026-09-17/cert.py
  - experiments/fpbs-transitive-retract-2026-09-17/cert_n5_j1.txt
  - experiments/fpbs-transitive-retract-2026-09-17/cert_n4_j2.txt
  - experiments/fpbs-transitive-retract-2026-09-17/scale.py
  - experiments/fpbs-transitive-retract-2026-09-17/scale_out.txt
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det.py
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det_j1.txt
  - experiments/fpbs-transitive-retract-2026-09-17/h1_det_j2.txt
---

**ESTABLISHED (Theorems 1–3 and Lemma R unconditional; Theorem 4 is an
equivalence with a named open conjecture in characteristic `p`, and
unconditional in characteristic 0).** Proofs are in
`research/fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps-proof.md`.

**Setting.**
- `L = F(a, b)`, `φ: a ↦ a, b ↦ b a b^-2`, `t_i = φ^i(b)`, `L_i = <a, t_i>`.
- `Q` is any finite right `L`-set, `n = |Q|`, and `F` is any field.
- `Γ_i(Q)`, the map `m: Γ_{j+1}(Q) → Γ_j(Q)`, and `deep_j(Q)`, `law_j(Q)`
  are as in [[fpbs-mal-depth-promotion-equals-overfold-merge-number]].
  A merge identifies two vertices of `Γ_{j+1}(Q)` over the same point of `Q`.
- `u_i = ∂t_i/∂b ∈ Z[L]` is the left Fox derivative, so `u_0 = 1` and
  `u_1 = 1 − c − cb` with `c = t_1`. This `u_1` is the element `u` of
  [[fpbs-mal-modp-promotion-certificates-are-fox-annihilators]].
- `k_w(Q) = dim_F { y ∈ F[Q] : y w = 0 }` for `w ∈ F[L]`, with the right
  action.
- `I_i ⊆ H_1(Sch(Q); F)` is the image of `H_1(Γ_i(Q); F)`, and `c_i` is the
  number of components of `Γ_i(Q)` (the `L_i`-orbits).
- `Q^{(j)}` is `Q` with `L` acting through `φ^j`.

**Theorem 1 (exact Fox identity).** For every `i ≥ 0` and every field,

```text
dim_F I_i = n + c_i − k_{u_i}(Q).
```

**Theorem 2 (homological certificate).** For every `j ≥ 0`, every `Q` and
every field,

```text
deep_j(Q)  ≥  B_j(Q) := (c_{j+1} − c_j) + dim I_j − dim I_{j+1}
                      = k_{u_{j+1}}(Q) − k_{u_j}(Q).
```

`B_j` is the best bound obtainable by counting how much each merge can add
to the `H_1(Sch(Q); F)`-image or remove from the component count, since each
merge does exactly one of these, by at most 1. The same bound holds for
`law_j`. So wherever `B_j(Q) = law_j(Q)` for some field, `deep_j(Q) = law_j(Q)`.
At `j = 0` this is Theorem 1 of the depth-0 node.

**Theorem 3 (chain rule and transport).** `u_{j+1} = φ^j(u_1) · u_j` in
`Z[L]`. Hence, for every field,

```text
0 ≤ k_{φ^j(u_1)}(Q) ≤ k_{u_{j+1}}(Q),   and   B_j(Q) ≤ k_{φ^j(u_1)}(Q) = k_{u_1}(Q^{(j)}).
```

So the depth-`j` certificate of `Q` is at most the depth-0 certificate of the
transported level `Q^{(j)}`.

**Theorem 4 (what the class is worth at every depth).** Let `X = lim Q_m` be
an essentially free profinite `L`-action.
- The action `X^{(j)}` (`L` acting through `φ^j`) is again essentially free,
  so its levels `Q_m^{(j)}` form a sofic approximation of `F_2`.
- *Characteristic 0.* `B_j(Q_m)/|Q_m| → 0` for every `j`. This uses Theorem 3,
  Elek–Szabó approximation along sofic approximations for matrices over
  `Q[F_2]`, and Linnell's theorem (`u_1 ≠ 0` acts injectively on `ℓ²F_2`).
- *Characteristic `p`.* `limsup_m B_j(Q_m)/|Q_m| > 0` for some `j` gives
  `limsup k_{u_1}(Q_m^{(j)})/|Q_m| > 0`. That contradicts
  positive-characteristic sofic Lück approximation (Jaikin-Zapirain,
  Conjecture 2.4 (1)–(2), `G = F_2`, `K = F_p`) for the same single element
  `u_1 = 1 − x − y` as at depth 0. This is open, not refuted.
- *`p`-levels.* If the image of `L` in `Sym(Q)` is a `p`-group, then
  `B_j(Q) = 0` in characteristic `p` at every depth. The reason is that
  `ε(u_i) = (−1)^i`, so each `u_i` is a unit of `F_p[P]`.

**Lemma R (retraction, all transitive levels).** Let `Q` be
`L_j`-transitive, `j ≥ 1`, `S = Stab_L(p)` and `K' = S ∩ L_j`.
- Then `rk K' = rk S = n + 1`.
- Every `J` with `K' ≤ J ≤ L` and `rk J ≤ rk K'` that has `K'` as a retract or
  a free factor equals `K'`. This uses Hopficity.
- This applies to `J = S`. It also applies to every single-seed hit
  `J = <K, g>` with an overfold seed in the free-fold setting of w17-pull
  (coincident orbits). There `rk K = rk K'`, and the no-drop lemma gives
  `rk J ≤ rk K + 1 − δ ≤ rk K'`.
- So the w17 retract kill, made at one level, holds on every `L_j`-transitive
  level.
- The `H_1`-split part of (G) is not universally dead. `H_1(K') → H_1(S)` is
  an isomorphism (`|det| = 1`) on 3192 of the 9504 `L_1`-transitive pairs of
  permutations with `n = 5` (`h1_det_j1.txt`).
- Theorem 2 shows that homology gives no linear bound in any case.

**Evidence (checks, not proof).**
- *`cert.py`.* It checks Theorem 1 two ways (chain-map kernel and Fox kernel),
  the transport bound of Theorem 3, and `deep_j ≥ B_j` against exact
  breadth-first search of `deep_j`. The fields are `Q, F_2, F_3, F_5`.
  - `n = 5, j = 1`: 200 random transitive levels (`cert_n5_j1.txt`);
  - `n = 4, j = 2`: 150 random transitive levels (`cert_n4_j2.txt`);
  - 0 violations. The certificate is sharp (`B = law`) on 33/200 and 24/150
    levels, all with `law = 1`.
- *`scale.py`.* On random levels up to `n = 400`, at `j = 0..3` and
  `p = 2, 3, 1000003`, `max B_j ≤ 2` (`scale_out.txt`). Meanwhile
  `law_1 ≈ 0.114 n` there (w17-follow).

**What dies (class kill, criterion 3).**
- *The class.* Every proof of `Q_j(X) > 0` at any depth `j ≥ 1`, or of the
  weak form `deep_j ≥ c · law_j` on towers, that bounds merges by first
  homology of the level graphs with field coefficients. This includes images
  and codimensions in `H_1(Sch(Q_m); F)` and component counts.
- *The invariant.* The Sylvester rank of the single element
  `u_1 = 1 − c − cb` on the transported levels `Q_m^{(j)}`.
- *The step where every member dies.* Theorem 2 makes the certificate exactly
  `k_{u_{j+1}} − k_{u_j}`. Theorem 3 bounds it by `k_{u_1}(Q_m^{(j)})`.
  Theorem 4 makes that `o(|Q_m|)`: unconditionally in characteristic 0, and
  in characteristic `p` unless Lück approximation fails for `u_1`.
- *What survives.* Non-abelian counts (generator numbers of relative
  quotients rather than their abelianizations), closure-order arguments such
  as (O-pair) and (RI), and the finite-level use of Theorem 2 to certify
  `deep = law` on individual levels with small `law`.
