---
rg: 2
id: thompson-f-is-lea-only-if-amenable-proof
kind: route
title: A local embedding of a ball containing the relators and a commutator is a homomorphism with nonabelian image, hence injective
target: thompson-f-is-lea-only-if-amenable
requires: []
---

**Import (trust surface).** Every proper quotient of `F` is abelian. Read on 2026-09-13 in the TeX
source of Burillo--Lodha--Reeves, arXiv:1509.04586 (`lm.tex`, line 104), verbatim: "Thompson's group
$F$ satisfies the property that $F'$ is simple, and every proper quotient of $F$ is abelian
\cite{cfp}", citing Cannon--Floyd--Parry's introductory notes. The primary source was not re-read.
Equivalently, every nontrivial normal subgroup of `F` contains `[F,F]`.

Let `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`.

**1. A ball that sees the relators.** Let `S` be the ball of radius `r` in `F` for the generators
`a, b`, with `r` at least the lengths of `R_1` and `R_2`. Then every prefix of each relator, and every
prefix of `c = [a,b] = a^-1 b^-1 a b`, lies in `S`. Since `F` is nonabelian, `c != e`.

**2. The local embedding is a homomorphism.** By LEA there are an amenable group `H` and a map
`phi : S -> H`, injective on `S`, with `phi(xy) = phi(x) phi(y)` whenever `x, y, xy` lie in `S`.
- `phi(e) = phi(e) phi(e)`, so `phi(e) = e_H`; and `phi(x^-1) = phi(x)^-1` for `x in S` with `x^-1 in S`.
- Put `alpha = phi(a)`, `beta = phi(b)`. Multiplicativity along consecutive prefixes of a word whose
  prefixes stay in `S` gives `phi(w) = w(alpha, beta)`.
- Applied to the relators: `R_i(alpha, beta) = phi(R_i) = phi(e) = e_H`.

So `a -> alpha`, `b -> beta` extends to a homomorphism `psi : F -> H`.

**3. The image is nonabelian.** By step 2, `psi(c) = c(alpha, beta) = phi(c)`, and `phi(c) != phi(e)`
by injectivity on `S`. So `psi(c) != e_H`. Since `c in [F,F]`, the normal subgroup `ker psi` does not
contain `[F,F]`.

**4. The homomorphism is injective.** A nontrivial normal subgroup of `F` contains `[F,F]` (import).
`ker psi` does not, so `ker psi = 1`.

**5. Conclusion.** `F` is isomorphic to the subgroup `psi(F)` of the amenable group `H`. Subgroups of
amenable groups are amenable, so `F` is amenable.

**Converse.** An amenable group is LEA: take `H = F` and the inclusion.
