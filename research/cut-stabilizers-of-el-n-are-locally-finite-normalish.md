---
rg: 2
id: cut-stabilizers-of-el-n-are-locally-finite-normalish
kind: claim
title: The half-orbit cut stabilizer in EL_n(LC(X,F_q)⋊Z) is an infinite locally finite normalish subgroup
distinct_from:
  cut-stabilizer-subgroups-of-el3-are-not-confined: that shows the same subgroup is not confined (its conjugates accumulate at the trivial subgroup); this shows every finite intersection of its conjugates is infinite, and that it is locally finite
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `X` is an infinite minimal subshift with shift `T`, `F_q` a finite field, `R = LC(X,F_q) ⋊_T Z`, `n ≥ 2` and `G = EL_n(R)`.
- For `y ∈ X`, `π_y(fu^k)δ_t = f(T^{t+k}y)δ_{t+k}` on `F_q^{(Z)}`, extended entrywise to `F_q^{(Z)} ⊗ F_q^n`.
- `S_y ≤ G` is the stabilizer of `V^{<0} = span{δ_t : t<0} ⊗ F_q^n` and `V^{≥0} = span{δ_t : t≥0} ⊗ F_q^n`.

**Theorem.**
1. The ring of `r ∈ R` whose `π_y(r)` preserves both half-lines is a directed union of finite rings `⊕_W M_{h(W)}(F_q)`, the
   tower algebras of Kakutani–Rokhlin partitions with base `B ∋ y`. So `S_y` is locally finite, and in particular amenable.
2. `S_y` is normalish: for all `t_1,…,t_m ∈ G`, the intersection `⋂_i t_iS_yt_i^{-1}` contains `{l ∈ SL_n(LC(X,F_q)) : l ≡ I on Z}`
   for a clopen `Z ≠ X`. That group is infinite.

The same holds modulo the finite centre of `G`.

**Consequences.**
- For `G_X`: `subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology`.
- Normalish (every finite intersection of conjugates is infinite) and not confined (conjugates accumulate at `{1}`,
  `cut-stabilizer-subgroups-of-el3-are-not-confined`) are compatible.
- The criterion `no-amenable-normalish-subgroup-implies-cstar-simple` cannot decide `subshift-elementary-groups-are-cstar-simple`.

**Proof:** `cut-stabilizers-el-n-locally-finite-normalish-proof`.
