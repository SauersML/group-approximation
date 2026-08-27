---
rg: 2
id: periodic-higman-mapping-torus-is-word-hyperbolic-proof
kind: route
title: Kill the invariant cyclic system by residual nilpotence and apply Mutanguha
target: periodic-higman-mapping-torus-is-word-hyperbolic
requires: []
---

## Direct proof

**Injectivity.**  The four images are

```text
A = a^-1 d^-1 a d,   B = b^-1 a^-1 b a,
C = c^-1 b^-1 c b,   D = d^-1 c^-1 d c.
```

For any `U, V` drawn from `{A,B,C,D}^(+-1)` with `V != U^-1`, inspection of the
junction shows at most one letter cancels.  So the image of a nonempty freely
reduced word is nonempty, and `phi` is injective.

**Descent in the lower central series.**  Each `phi(x_i)` is a commutator, so
`phi(F) <= gamma_2(F)`, and inductively

```text
phi^n(F) <= gamma_(2^n)(F).                                        (1)
```

**No invariant cyclic system.**  Mutanguha's criterion says an ascending HNN
extension of a free group along an injective endomorphism is word-hyperbolic
exactly when there is no Baumslag--Solitar obstruction, i.e. no `g != 1`,
`k >= 1`, `r != 0` with `phi^k(g) ~ g^r`.  Suppose such a system existed.
Iterating gives `phi^(kn)(g) ~ g^(r^n)`, so by `(1)`

```text
g^(r^n) in gamma_(2^(kn))(F).
```

Every free nilpotent quotient `F / gamma_j(F)` is torsion free, so the power may
be stripped: `g in gamma_(2^(kn))(F)` for every `n`.  Free groups are residually
nilpotent, `intersection_j gamma_j(F) = 1`, hence `g = 1`, a contradiction.

Mutanguha's characterization now gives word-hyperbolicity of `M_phi`.

## Literature used

Mutanguha, *The dynamics and geometry of free group endomorphisms* — the
hyperbolicity criterion for ascending HNN extensions.  Borisov--Sapir,
*Polynomial maps over finite fields and residual finiteness of mapping tori of
group endomorphisms* — used only in the claim's remark that `M_phi` itself is
residually finite.
