---
rg: 2
id: uniquely-ergodic-action-sofic-iff-topological-microstates
kind: claim
title: A uniquely ergodic action of a sofic group on a compact metric space is sofic iff finite almost-actions map almost equivariantly into the space
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-microstates-2026-09-13.md
distinct_from:
  finite-equidistributed-orbits-give-sofic-action: that builds models from honest finite invariant subsets and needs their equidistribution as a hypothesis; this accepts arbitrary finite almost-actions with approximately equivariant marks and gets equidistribution for free from unique ergodicity
  sofic-action-with-sofic-ergodic-components-is-sofic: that assembles models of ergodic components; this replaces measure-theoretic models by topological microstates for a single uniquely ergodic system
---

**ESTABLISHED (unreviewed).** Let a countable sofic group `Γ` act by homeomorphisms on a compact metric
space `(X,d)`, preserving a Borel probability measure `μ`. For finite `F ∋ 1` and `ε > 0`, an
`(F,ε)`-microstate is a finite set `V` with maps `σ : F → Sym(V)` and `y : V → X` such that

```text
|{v : σ(s)σ(t)v != σ(st)v}| <= ε|V|    (s, t, st ∈ F),
|{v : d(y(σ(s)v), s·y(v)) >= ε}| <= ε|V|    (s ∈ F).
```

1. If `Γ ↷ (X,μ)` is sofic (Păunescu Definition 1.4), then `(F,ε)`-microstates exist for all `F` and `ε`.
2. If `μ` is the only `Γ`-invariant Borel probability measure and microstates exist for all `F` and `ε`,
   then `Γ ↷ (X,μ)` is sofic.

Freeness of `σ` is not required, and neither is any distribution condition on `y`. Unique ergodicity
forces the pushed-forward counting measures to converge to `μ`. For uniquely ergodic systems, soficity
is therefore a property of the topological dynamical system alone.

**Credit.** This is close in spirit to Kerr--Li's topological microstates and variational principle, but
no source was checked for this exact statement. The proof uses only Lemma LC of the mixing-transfer
artifact.

Proof in `uniquely-ergodic-action-sofic-iff-topological-microstates-proof`.
