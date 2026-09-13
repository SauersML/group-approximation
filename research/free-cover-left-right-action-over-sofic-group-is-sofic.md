---
rg: 2
id: free-cover-left-right-action-over-sofic-group-is-sofic
kind: claim
title: The free-cover left-right action over any sofic group is a sofic action
distinct_from:
  mikhailova-left-right-action-sofic-for-lea-quotients: that builds charts from amenable models of LEA quotients; this uses a permutation frame over an arbitrary sofic approximation and so reaches every sofic quotient.
  mikhailova-left-right-action-current-frontier: that records LEA quotients as the positive frontier and the nonsofic host as open; this moves the positive frontier to all sofic quotients, so a nonsofic free-cover left-right action needs a nonsofic quotient.
  mikhailova-left-right-soficity-is-one-color-code: that is the exact color-code criterion (MLF2); this writes down such a code, the color s^-1(p) on Sym(A) x A, whenever the quotient is sofic.
  g-x-free-set-actions-sofic-when-kernel-amenably-separable: that handles every stabilizer whose kernel in one factor is amenably separable; this handles full-projection stabilizers over sofic quotients, whose kernels need not be amenably separable.
---

ESTABLISHED (unreviewed). Soficity of an action is GKP Definition 2.1(5).

Let `Q` be a countable sofic group, `F`, `F'` countable free groups and
`φ_1 : F -> Q`, `φ_2 : F' -> Q` homomorphisms. Then the action

```text
F x F' ↷ Q,        (u,v).x = φ_1(u) x φ_2(v)^-1                  (LR)
```

is sofic.

Equivalently, for every `L <= F x F'` with `p_1(L) = F` and `p_2(L) = F'`
whose Goursat quotient `F/(L ∩ F)` is sofic, the coset action
`F x F' ↷ (F x F')/L` is sofic. In particular:

- the Mikhailova left-right action `(MLF1)` of
  [[mikhailova-left-right-action-current-frontier]] is sofic for **every**
  sofic `H`, not only LEA `H`;
- by GKP Theorem 3.7 ([[gkp-free-generalized-wreath-soficity]]) the
  Mikhailova rope `< F x F, v | [v, M_H] = 1 >` is sofic for every sofic `H`.

DERIVATION [[free-cover-left-right-action-over-sofic-group-is-sofic-proof]].

## The model in one line

From a sofic approximation `σ : Q -> Sym(A)`, extend `σ ∘ φ_1` and `σ ∘ φ_2`
freely to exact homomorphisms `λ`, `ρ`. On `Ω = Sym(A) x A` let `F` act on
the frame by `s -> λ(u)s` and `F'` on the point by `p -> ρ(v)p`, and label
`x in Q` at `(s,p)` by `s^-1(σ(x)p)`. The coordinates commute exactly. The
labels are injective and equivariant off the small set of points `p` where
`σ` fails multiplicativity or freeness on the finite window.

In the color-code form `(MLF2)` this is `a(u) = λ(u) x 1`,
`b(v) = 1 x ρ(v)^-1`, and color `ξ(s,p) = s^-1(p)`. Then `a(n)ξ = ξ` for
`n in N`, `a(w)b(w)ξ = ξ`, and `a(w)ξ` differs from `ξ` almost everywhere for
`w ∉ N`. The color is diffuse, as
[[mikhailova-color-code-must-escape-finite-palettes]] requires, and there is no
global `Q`-valued coordinate, so the amenability no-go (MLQ3) of
[[mikhailova-left-right-action-sofic-for-lea-quotients]] does not apply.

## Consequences

1. **Negative direction.** A nonsofic set action of `F x F'` whose stabilizer
   has full projections needs a **nonsofic** Goursat quotient. In the compiler,
   `(MLF1)` is sofic whenever the Higman host is sofic. On the branches where
   the host contains a nonsofic seed, the question stays open.
2. **What is not claimed.** The converse, that soficity of `(LR)` forces `Q`
   sofic, is not known. The one-sided restriction `F ↷ Q` is sofic for every
   `Q` (GKP Theorem 2.19), so any converse must use the commuting right factor.
