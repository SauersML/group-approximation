---
rg: 2
id: k-inexact-module-triple-refutes-trivial-coefficient-bc
kind: claim
title: A K-theory exactness defect for the crossed products of a module quotient refutes Baum--Connes with trivial coefficients for the module group or its quotient
distinct_from:
  amenable-kernel-bc-transfer-and-ktop-half-exactness: that imports the transfer theorem and half-exactness; this combines them with the Higson--Lafforgue--Skandalis diagram chase on the triple C_0(U) -> C(V^) -> C(W^perp), turning a coefficient defect into a failure for a group with trivial coefficients.
  bgw-trivial-coefficient-agreement-is-open: that concerns the exact-crossed-product reformulation; this concerns the classical reduced map and a specific group-realizable coefficient triple.
---

**ESTABLISHED** by `k-inexact-module-triple-refutes-trivial-coefficient-bc-proof`.

**Setting.**
- `G` is a countable discrete group, and `V` a countable `Z[G]`-module (an abelian group
  with a `G`-action).
- `W <= V` is a submodule, `X = V^` (compact dual group), `Z = W^perp ≅ (V/W)^` (closed
  invariant subgroup), and `U = X \ Z`.
- `Γ = V ⋊ G`, and `Γ' = Γ / W = (V/W) ⋊ G`.

Then `C*_r(Γ) = C(X) ⋊_r G` and `C*_r(Γ') = C(Z) ⋊_r G`. The quotient map
`q : C*_r(Γ) -> C*_r(Γ')` is restriction of functions, and its obvious ideal is
`C_0(U) ⋊_r G`.

**Theorem.** Suppose that for some `j ∈ {0, 1}` the sequence

```text
K_j( C_0(U) ⋊_r G )  ->  K_j( C*_r(V ⋊ G) )  ->  K_j( C*_r((V/W) ⋊ G) )
```

is not exact at the middle term. Then at least one of the following holds:
- the reduced assembly map of `V ⋊ G` is not surjective in degree `j`;
- the reduced assembly map of `(V/W) ⋊ G` is not injective in degree `j`.

Either way some countable group violates the Baum--Connes conjecture with **trivial**
coefficients. If `G` and `V` are finitely generated (the latter as a module), both groups are
finitely generated.

**Remarks.**
- **How it relates to the known counterexamples.** Higson--Lafforgue--Skandalis (GAFA 12
  (2002); context, not imported) run this chase with commutative coefficients over a Gromov
  monster. Those coefficients are not duals of modules.
- **Model test.**
  - *Trivial model.* With `W = V` the quotient is `C*_r(G)`. The sequence is exact by the
    Buss--Echterhoff--Willett erratum, Lemma A.1 (`bgw-trivial-coefficient-agreement-is-open`),
    so the hypothesis fails, as it must.
  - *Exact groups.* For exact `G`, reduced crossed products preserve exact sequences
    (Kirchberg--Wassermann; context, not imported), so again no instance exists. A witness
    needs a non-exact `G`.
- **Which failure occurs.** The theorem does not say. Nothing in the graph proves injectivity
  of assembly for the quotient groups.

**Integration boundary, 2026-09-20.** The sufficient implication is
complete; `some-nonexact-group-has-a-k-inexact-module-triple` is still
the missing existential input. It requires an actual middle-term
K-class y with q_*(y)=0 and y outside im i_*, not merely a nonzero
C*-kernel. The passage to ordinary assembly uses amenable-kernel
partial assembly with its finite-subgroup preimage hypotheses; it
does not assert permanence from a positive normal subgroup alone.
See the [integration ledger](artifacts/bc-nonhyperlinearity-integration-2026-09-20.md).

The [further attempt](artifacts/Cairn_Baum_Connes_General_Attempt.md)
identifies the required defect exactly with `im p_* ∩ ker q̄_*` in
`K_j(C/J)` via
[quotient localization](module-k-defect-is-liftable-quotient-kernel.md).
The [equivalent existential input](some-module-quotient-has-a-nonzero-liftable-kernel-class.md)
remains OPEN. All bounded positive traces on C/J kill candidate
degree-zero classes; this restricts detection and does not prove that
the sufficient hypothesis fails.
