---
rg: 2
id: two-point-data-yields-invariant-projection
kind: claim
title: Two-point data assembles into a Γ-invariant projection moved by the marked element
distinct_from:
  two-point-orbit-approximation: that is the approximation claim itself; this is the bridge lemma showing its truth would manufacture a window-free ultraproduct object — a sofic representation with a Γ-invariant projection that σ(h) moves by a definite amount.
  pair-constraint-graph-criterion: that analyzes label data combinatorially at a fixed window; this spends the window quantifier entirely, trading the fixed-window structure for an exact statement in the ultraproduct.
  normal-closure-fixes-gamma-fixed-algebra: that is the rigidity which the assembled object contradicts; this is the assembly, and the two are kept separate because each could fail independently.
---

Let `(p,q) = (Γ, hΓ)` be the marked pair of the Kun--Thom Theorem E pair.

**Theorem.**  If `two-point-orbit-approximation` holds — two-point data at
`(p,q)` for every finite window `F ⊆ G` and every `ε > 0` — then there
exist a **sofic representation** `σ : G → S_𝒰` (i.e. `d(σ(g), 1) = 1` for
every `g ≠ 1`) and a projection `a` in the diagonal algebra `D_𝒰` with

```text
σ(γ)a = a  for every γ ∈ Γ,        τ(a △ σ(h)a) ≥ c > 0,
```

for an absolute constant `c` (any `c < 1/2` is achievable).

The content is threefold.  First, the **free invariance**: the
equivariance clause of the two-point definition, read at `γ ∈ Γ` and slot
`p`, literally says the `p`-label function `f_p(s) = j_s(p)` is
`Γ`-invariant on the good set — the definition hands over exact
`Γ`-structure with no reconstruction.  Second, the **separation**: reading
the clause at `h` and slot `q` gives `f_p(φ(h)s) ≠ f_p(s)` on the good
set, and a random level set of `f_p` converts that into a projection
moved by `σ(h)` on half the mass.  Third, the **soficity repair by tensoring**: the assembled `σ` need not
be a sofic representation (the flip models have `|A| = 2`), but tensoring
each model with the free left-translation action of a finite quotient of
`G` (which exists — `G` is residually finite, Theorem E) leaves the
multiplicativity defects and the separation untouched while making every
`σ(g)`, `g ≠ 1`, fixed-point free on the nose: `d(σ(g),1) = 1` with no
amplification and no case split.  The repair covers bounded `|A|` — where
a disjoint-union repair provably cannot — and the constant `c = 1/2` is
achieved, not merely approached.
