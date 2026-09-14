---
rg: 2
id: subshift-elementary-group-simple-iff-infinite-minimal
kind: claim
title: For a nonempty subshift X, a field k and n ≥ 3, EL_n(LC(X,k) ⋊ Z) is simple modulo its centre iff X is infinite and minimal
distinct_from:
  steinberg-algebra-simple-iff-minimal-effective: that is the ring-level criterion for Steinberg algebras (an import); this is the group-level criterion for EL_n over subshift algebras, whose only-if direction passes a nonzero ideal to a noncentral proper normal subgroup.
  steinberg-elementary-groups-are-simple-mod-centre: that is the if direction for every minimal effective ample groupoid; this adds the converse for subshifts over Z, so the hypothesis "infinite minimal" in the note is sharp.
---

**ESTABLISHED (unreviewed)** by `subshift-elementary-group-simple-iff-infinite-minimal-proof`.

**Statement.** Let `X ⊆ A^Z` be a nonempty subshift over a finite alphabet, `k` a field, `n ≥ 3`, `R_X = LC(X,k) ⋊_T Z`, and `G = EL_n(R_X)`. Then `G/Z(G)` is simple if and only if `X` is infinite and minimal.

If `X` is not minimal, or is a finite orbit, then `R_X` has a nonzero proper ideal `I`. The kernel of `G → EL_n(R_X/I)` is then a noncentral proper normal subgroup of `G`.

**Examples.**
- `X = {a^∞}`: `R_X = k[u,u^(-1)]`, and reduction modulo `u − 1` maps `G` onto `SL_n(k)` with kernel containing `e_12(u−1)`.
- `X` = the orbit closure of `…0001000…`: restriction to the fixed point `{0^∞}` gives `G → EL_n(k[u,u^(-1)])` with kernel containing `e_12(e_U)` for any clopen `U` avoiding `0^∞`.

Related material on normal subgroups of non-minimal subshift groups (artifacts only, no claim): `research/artifacts/pestov91-cycle-core-exact-mf-reflection-2026-09-13.md`, `research/artifacts/pestov91-seam-normal-lattice-2026-09-13.md`.

**Review (sk-verify-5, 2026-09-13): PASS.** If: the Steinberg criterion. Only if:
- restriction to a proper closed invariant subset is a surjective ring homomorphism with `e_U` in the kernel;
- a finite orbit gives `R → End_k(k^X)` with `u^p − 1` in the kernel;
- the kernel of `EL_n(φ)` contains the noncentral `e_12(r)`, and `K Z(G) ≠ G` because `EL_n(S)` is nonabelian.

See `research/artifacts/sk-review-5-2026-09-13-part1.md` §4.
