---
rg: 2
id: hidden-labels-import-cross-context-commutation
kind: claim
title: Any coset refinement of a Boolean context game makes a variable of a non-rectangular context commute with the far neighbour on a split piece
artifacts:
  - research/artifacts/ex-kac-quantum-bijection-2026-09-13.md
distinct_from:
  exact-label-coset-refinements-are-affine: that treats label-exact refinements and gets affine allowed sets; this allows hidden shared labels, padding and arbitrary groups, and gets a three-context commutation condition that a factor model fails.
  coset-refinement-forces-rectangular-central-splitting: that is a two-question condition, vacuous for context games whose edges only check shared variables; this is a three-context condition that stays non-vacuous there.
  port-generated-square-completions-force-coset-support: that treats completions inside the port algebra; this treats every coset refinement, including padding outside it.
---

**ESTABLISHED** by `hidden-labels-import-cross-context-commutation-proof`.
Reviewed PASS by independent re-derivation (ex-verify2-quantum-l2, 0360cef67f,
`research/artifacts/ex-review2-quantum-l2-2026-09-13-part8.md` §8.3).  One
justification in (H7) was corrected forward on the proof route.

**Setting.**

- `B` is a Boolean constraint system in context form and `G_B` its context
  game, as in `exact-label-coset-refinements-are-affine`.
- `R` is any coset refinement of `G_B`
  (`coset-refinement-forces-rectangular-central-splitting`): any finite
  groups, any padding, any blocks.
- `tau` is a tracial state on `A(R)` and `M` its GNS algebra.
  - `P_c` is the pushed-forward PVM of context `c`.
  - `X_v` is the pushed-forward symmetry of variable `v`.

**Theorem.**  Let `c` be a context, and let `u, w in c` with `u in c ∩ c'` and
`w in c ∩ c''` for contexts `c', c'' != c`.  Suppose the restriction of
`Allowed_c` to `(u, w)` misses at least one of the four patterns (for example
NAND).  Then there is a projection `m in M` commuting with `P_c`, `P_(c')` and
`P_(c'')` such that

```text
[X_u, P_(c'')^b] m = 0      and      [X_w, P_(c')^(b')] (1 - m) = 0
for all answers b of c'' and b' of c'.                                  (HL)
```

In words: on `m` the far context `c''` sees `u`; on `1 - m` the far context
`c'` sees `w`.

**Corollaries.**

1. **Factor test.**  Suppose `W*(P_c, P_(c'), P_(c''))` is a factor and both
   `[X_u, P_(c'')]` and `[X_w, P_(c')]` are nonzero.  Then `tau` does not
   factor through any coset refinement.
2. **Synchronous sources.**
   - **Presentation.**  Present a synchronous game with one one-hot context
     per question on the variables `x_(q,a)`, and one NAND context
     `{x_(q,a), x_(q',a')}` per forbidden pair with `q != q'`.  This is the
     shape described in
     `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`.
   - **Conclusion.**  If a perfect trace factors through a coset refinement,
     then for every forbidden pair there is a projection `m` commuting with
     `P_q` and `P_(q')` such that:
     - `P_q^a` commutes with `P_(q')` on `m`;
     - `P_(q')^(a')` commutes with `P_q` on `1 - m`.
   - **Factor pair algebras.**  If the pair algebra is a factor, one of
     `P_q^a`, `P_(q')^(a')` must be `0` or `1`.
   - **Equivalent form (lane ex2-kac-forbidden-pair).**  On a perfect trace
     this split is equivalent to orthogonal central supports of `P_q^a` and
     `P_(q')^(a')` in `W*(P_q, P_(q'))`.  Over all forbidden pairs it is
     (RCS) of `coset-refinement-forces-rectangular-central-splitting`.  Every
     perfect trace of a constraint-variable presentation passes it
     (`forbidden-pair-splits-are-central-rectangle-splittings`).
3. **Hidden labels are not free.**  The shared labels that
   `exact-label-coset-refinements-are-affine` left open must carry variables
   of `c` to neighbours that do not contain them.

**Model tests.**

- **A classical solution passes**, with `m = 1`.
- **A real perfect model fails.**  Take `c = {u,w}` with NAND,
  `c' = {u,y}` and `c'' = {w,z}` with all patterns allowed, in `M_3` with the
  normalized trace.
  - `X_u` and `X_w` are diagonal with bits `(0,0,1)` and `(0,1,0)` in the
    basis `e_00, e_01, e_10`.
  - `X_y` swaps `e_00` and `e_01`, and `X_z` swaps `e_00` and `e_10`.
  - Every context commutes and has allowed spectrum, so the model is perfect.
  - The four symmetries generate `M_3`, while `[X_u, X_z] != 0` and
    `[X_w, X_y] != 0`.
  - By Corollary 1 this trace factors through no coset refinement, over any
    groups and with any padding.
