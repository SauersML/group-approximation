---
rg: 2
id: accessible-shell-inputs-admit-no-shift-normalizing-enumeration
kind: claim
title: For every accessible input that is not virtually cyclic, in particular every finitely presented one, no nonzero power of the cofinite shift normalizes the regular near copy
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that treats one-ended inputs only and says "Inputs with infinitely many ends are not treated"; this covers all accessible non-virtually-cyclic inputs, including P*Z, free groups and virtually free groups, by an end Euler measure instead of the unique infinite component, and also allows the twisting endomorphism to have proper finite-index image.
  shell-prefix-core-detects-finite-ray-enumerations: that classifies shift powers COMMUTING near infinity with the input (untwisted), via finite-ray germ groups; this excludes conjugation into the regular copy through any injective endomorphism, where no finite-ray structure is available.
  shell-ascending-gate-is-a-finite-window-inclusion: that reduces the gate to s^-eps lambda(P) s^eps <= W_N for some window N; this proves N = 0 is impossible for every finitely presented non-virtually-cyclic input, so every gate witness needs N >= 1.
artifacts:
  - experiments/window-zero-enumerations-2026-09-17/end_measure_check.py
  - research/artifacts/shell-envelope-general-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty
claimed).

Let `P` be an infinite finitely generated accessible group that is not
virtually cyclic, for instance any finitely presented such group. Let `S` be
a finite generating set and `nu: P -> N` any bijection. Write
`lambda_g(nu(h)) = nu(gh)` and `s: n -> n+1`. Fix an integer `m != 0`. Then
there is no map `phi: S -> P` such that, for every `g` in `S`,

    s^m lambda_g s^-m = lambda_(phi(g))   near infinity.

**Consequences** for `R_nu = <lambda(P), s>` and the gate
`shell-germ-fp-is-an-ascending-hnn-gate`:

1. For every such input and every enumeration, `s^m lambda(P) s^-m` is not
   contained in `lambda(P)`, for any `m != 0`. So the window `N = 0` never
   passes the finite-window gate `shell-ascending-gate-is-a-finite-window-inclusion`,
   and `B = lambda(P)` is never an ascending HNN base. Every germ-level
   finite-presentation witness must use a window `N >= 1`, like the square
   spiral with `N = 2`.
2. `ker(eta)` is never `lambda(P)`, and `R_nu` is never the semidirect
   product `lambda(P) x| <s>` with `s` acting by an endomorphism of the
   regular copy.
3. Through the parity fiber product, no nonzero even power of `tau`
   normalizes `rho(P)` in the shell germ group `Q`.

This kills the "window-zero" route through the cofinal input class `P*Z`.
Every finitely presented group `P_0` embeds in the infinitely-ended,
finitely presented and decidable (when `P_0` is) input `P_0*Z`. So a
shift-normalizing enumeration of `P_0*Z` would have given `R_nu`
finitely presented as an ascending HNN extension of `P_0*Z`, and the gate
with `N = 0`. That class is empty.

The mechanism is an index count. The shift is affine
`y -> phi(y) c_i` on each infinite component of the Cayley graph minus a
finite set. The components' images, pulled back coset by coset, give
`k = [P : phi(P)]` near-partitions of `P` by right translates of the same
pieces. An end Euler measure `mu`
(`accessible-non-virtually-cyclic-groups-carry-end-euler-measures`) turns
this into `(k - 1) * mu(Pbar) = m`. Iterating to `s^(mn)` with `phi^n`
gives `(k^n - 1) * mu(Pbar) = mn` for all `n >= 1`, which is impossible.

The hypothesis "not virtually cyclic" cannot be dropped. The zigzag
enumeration of `Z` satisfies `s lambda_1 s^-1 = lambda_(-1)` near infinity
(see `one-ended-shell-shift-normalization-proof`). For `Z`, the same brute
force in the script finds piecewise translations with nonzero index, while
for `F_2` all 85 twisted depth-one near-bijections found (five
automorphisms, multipliers of length at most 2) have index 0.

Not treated: inaccessible finitely generated inputs, and windows `N >= 1`,
where the square spiral shows that no universal obstruction exists.

DERIVATION
accessible-shell-shift-normalization-proof
