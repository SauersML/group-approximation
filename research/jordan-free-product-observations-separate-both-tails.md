---
rg: 2
id: jordan-free-product-observations-separate-both-tails
kind: claim
title: Unipotent Jordan automorphisms of Z^r free product F_s admit V observations separating both tails
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

**OPEN — submitted explicit observation lemma pending independent review.**

For `r,s≥1`, let `D=Z^r*F_s` with commuting generators `a_i` and
free generators `c_j`. Define `φ(a_1)=a_1`, `φ(a_i)=a_{i-1}a_i`
for `i>1`, and `φ(c_j)=c_j`. Choose a freely generating tuple
`α,γ_1,…,γ_s` in `V`, and define `ρ(a_1)=α`, `ρ(a_i)=1` for
`i>1`, `ρ(c_j)=γ_j`. Then `φ` is an automorphism, `D` has a finite
classifying space, and `ρφ^n(g)≠1` for every nonidentity `g` and all
but finitely many integers `n`. In particular both separation conditions
hold, although `ρ` is noninjective for `r≥2`.

## Attempts

The Jordan formula observes an abelian exponent vector `v` as
`α^{Σ_i v_i C(n,i-1)}` for all integers `n`. Each nonzero vector gives
a nonzero polynomial with finitely many roots. A reduced free-product
word has only finitely many abelian syllables, so outside a finite set
all survive and alternate with nontrivial free `γ_j` syllables.
The wedge of a torus and circles gives the finite classifying space.
Verify the negative-integer Jordan formula, the homomorphism and
automorphism conventions, and the free-product normal-form argument.
Existence of the free subgroup of `V` uses prefix ping-pong or the
classical input noted in artifact §6. This elementary proposed lemma
has not yet received an independent mathematical certification.
