---
rg: 2
id: lcs-compiler-target-is-goal-equivalent
kind: claim
title: The perfect-completeness constant-soundness LCS compiler is equivalent to finitely presented nonhyperlinearity
distinct_from:
  canonical-reverse-kleene-compiler-is-goal-equivalent: that treats the canonical-profile reverse-Kleene compiler interfaces (CPK) and (MGC); this treats the binary LCS compiler interface (PC1)-(PC2) consumed by non-hyperlinear-from-perfect-completeness-lcs-compiler.
  perfect-completeness-constant-soundness-lcs-compiler: that is the existence target itself; this proves that its bare existence is exactly as strong as the existence of a finitely presented nonhyperlinear group, so no weaker intermediate lies at that seam.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that proves the one-instance equivalence between affine-safe non-CE BCS traces, non-CE perfect LCS instances and nonhyperlinear groups; this lifts the LCS endpoint to the machine-indexed compiler interface.
  pcp-subroutes-to-both-hs-dehn-orientations-share-lin-barrier: that locates both HS-Dehn orientations at one affine-LIN barrier; this proves that crossing that barrier by any total LCS compiler with (PC1)-(PC2) is goal-equivalent.
---

**ESTABLISHED.**  The following existence statements are equivalent.

1. There is a finitely presented nonhyperlinear group.
2. There is a finite binary linear constraint system with a perfect tracial
   state and no perfect Connes-embeddable state.
3. There is a total computable map `M -> L_M` to finite binary linear
   constraint systems satisfying `(PC1)` and `(PC2)` of
   `perfect-completeness-constant-soundness-lcs-compiler`.

`1 <=> 2` is the Paddock--Slofstra solution-group endpoint (Proposition 5.8),
recorded in `locally-affine-support-bcs-is-exactly-the-lcs-boundary`.
`3 => 1` is `re-oriented-lcs-compiler-gives-nonhyperlinear-group`, which
moreover makes the group explicit once the compiler is given effectively.

For `2 => 3`, fix `L_*` as in statement 2 and use the constant compiler

```text
L_M = L_*          for every machine M.                      (LGE1)
```

- `(PC1)`: a perfect tracial state gives a representation of the solution
  group with `J = -I`, so `J != 1` in `Gamma_(L_*)`, whatever `M` does.
- `(PC2)`: `L_*` is a finite game.  If `omega_q(L_*) = 1`, finite-dimensional
  strategies with value tending to one give a perfect state in a matrix
  ultraproduct, i.e. a perfect Connes-embeddable state.  There is none, so
  `omega_q(L_*) < 1`, whatever `M` does.

The constant map is total and computable, so statement 3 holds.  The proof is
`lcs-compiler-goal-equivalence-proof`.

## What this settles about the affine barrier

The direction `2 => 3` is deliberately vacuous: it uses no decoder, no gap
amplification and no recursion.  Statement 3 therefore carries no content
beyond statement 1.  Crossing the affine pp-definability barrier of
`selector-gated-equality-is-not-affine-pp-definable` by **any** total LCS
compiler with `(PC1)-(PC2)`, whatever language or reduction it starts from,
is exactly as hard as producing a finitely presented nonhyperlinear group.
The compiler is a reformulation of the goal, not an intermediate step.

Other target languages do not give a cheaper seam either:

- **Group-valued compilers reduce to this one.**  A total compiler to
  finitely presented groups with a marked central involution, nontrivial on
  halting inputs and approximately trivial on nonhalting inputs, composes
  with Slofstra's effective embedding
  (`slofstra-solution-group-embedding-preserves-marked-involutions`, with
  approximate triviality transferred by
  `marked-approximate-radical-survives-solution-group-embedding`) to an LCS
  compiler with `(PC1)-(PC2)`.  So it is again statement 3.
- **Groupified gadgets carry only affine profiles.**  Every ordinary-group
  central-character extension profile is affine
  (`central-character-profiles-affine-under-odd-tensor-products`), so no
  group gadget in any language exactly carries a nonaffine predicate together
  with all its singleton branches.
- **Nonaffine languages give algebras, not groups.**  A compiler into a
  nonaffine Boolean language yields non-Connes-embeddable synchronous
  algebras, which MIP* = RE already supplies.  Upgrading such an algebra to a
  group is the group-valued case above.
- **Model selection and instance changing do not help.**
  `oracular-affine-support-replacement-has-no-intermediate-regime` refutes
  same-instance model selection and shows the instance-changing affine-safe
  endpoint is goal-equivalent; `jnvwy-active-output-has-no-affine-safe-perfect-model`
  excludes affine-safe perfect models of the unchanged JNVWY verifier; and
  `finite-affine-profile-or-removes-pcpp-section-gate` leaves source affine
  safety as the only input of the Culf--Mastel chain.

What remains at this seam is therefore not a better compiler but a direct
construction of statement 2, for example a verifier family whose halting
perfect models are affine-safe on every edge.

## Scope

- Statements 1-3 are existence statements.  The root `non-hyperlinear-group`
  asks for an explicit group.  Only `3 => 1` produces one, and only from an
  effective compiler; the constant compiler `(LGE1)` is effective only once
  `L_*` is written down.
- No quantitative soundness constant is claimed: `(PC2)` asks only
  `omega_q < 1`.
