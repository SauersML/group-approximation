---
rg: 2
id: thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f-proof
kind: route
title: The two F relators hold exactly for x_2 x_0^-1 and x_1 x_0^-1, which do not commute, and every proper quotient of F is abelian
target: thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f
requires: []
artifacts:
  - research/artifacts/hl-thompson-f-2026-09-13.md
---

**Imports (trust surface).**
1. *Finite presentation.* J. T. Moore, arXiv:0905.1118v7, `main.tex` l.102–108, read on MSI
   2026-09-13: "The standard presentation of $F$ is infinite, with generators $x_i$ $(i \in \Nbb)$
   satisfying $x_i^{-1} x_n x_i = x_{n+1}$ for all $i < n$. It is well known, however, that $F$ admits
   the finite presentation \[ \Seq{A,B \ |\ [AB^{-1},A^{-1}BA] = [AB^{-1},A^{-2}BA^2]= \mathrm{id}} \]
   (see \cite{CFP})." Here `A = x_0`, `B = x_1`; Cannon–Floyd–Parry was not re-read.
2. *Proper quotients.* Every proper quotient of `F` is abelian. This is the import already recorded in
   `thompson-f-is-lea-only-if-amenable-proof` (Burillo–Lodha–Reeves, arXiv:1509.04586, `lm.tex` l.104,
   citing Cannon–Floyd–Parry).

**Step 1 (a faithful exact model).** Let `X0` and `X1` be the PL homeomorphisms of `[0,1]` with
breakpoints `(0,0),(1/2,1/4),(3/4,1/2),(1,1)` and `(0,0),(1/2,1/2),(3/4,5/8),(7/8,3/4),(1,1)`, with
product `f·g = f∘g`. The program `experiments/thompson-f/hl/plsub.py` represents maps by exact rational
breakpoints and checks:
- both relators of import 1 are the identity for `(A, B) = (X0, X1)`;
- `x_j x_i = x_i x_(j+1)` for `1 <= i < j <= 3` and `x_j x_0 = x_0 x_(j+1)` for `j <= 3`, with
  `x_(n+1) = X0^-n X1 X0^n`;
- `[X0, X1] != id`.
So `x_0 -> X0`, `x_1 -> X1` defines a homomorphism from `F`. Its image is nonabelian, so by import 2 its
kernel is trivial. Group computations in this model are computations in `F`.

**Step 2 (the relators for p, q).** In the model, `p = X2·X0^-1` and `q = X1·X0^-1` have the
breakpoints listed in the claim. The same program checks that both relators of import 1 are the
identity for `(A, B) = (p, q)`, and that `[p, q] != id`. So `x_0 -> p`, `x_1 -> q` defines a
homomorphism `ψ : F -> F`. The kernel of `ψ` is a normal subgroup whose quotient `ψ(F)` is nonabelian,
so by import 2 the kernel is trivial.

A search over all freely reduced words of length `<= 4` in `p^±1, q^±1` found `(p, q)` as the unique
pair of maximal length 1 with these properties (`plsub.py` output in the artifact).

**Step 3 (independent cross-check).** `experiments/thompson-f/hl/plcheck2.py` does not merge breakpoints.
It defines `X0, X1` and their inverses as point maps and evaluates each word by composing them pointwise
at 21025 dyadic points (20000 random points with denominator `2^20` and all points `k/1024`). Both relators
for `(p, q)` fix every point, `[p, q]` moves 13143 of them, and the monoid relations
`x_1 x_0 = x_0 x_2`, `x_2 x_1 = x_1 x_3` hold at every tested point. This cross-check is a consistency
test, not a second proof.
