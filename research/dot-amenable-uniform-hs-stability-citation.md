---
rg: 2
id: dot-amenable-uniform-hs-stability-citation
kind: route
title: Import De Chiffre--Ozawa--Thom Theorem 5.2 in the normalized trace norm on M_n
target: dot-amenable-uniform-hs-stability
requires: []
---

Established by M. De Chiffre, N. Ozawa and A. Thom, *Operator algebraic approach to inverse and stability theorems
for amenable groups*, arXiv:1706.04544v2 (23 Jun 2017). Text extracted from the arXiv PDF on 2026-09-18 (ligatures normalized, norm
bars written `|| ||`).

**Setting (Section 2, verbatim).** "We define M∞ := M ⊗̄ B(ℓ2(N)) and view M as a corner of M∞."

**Definition 5.1 (verbatim).** "If G is amenable, a map ϕ: G → H is called a mean ε-homomorphism if for all g ∈ G
E_h d(ϕ(gh), ϕ(g)ϕ(h)) < ε. ... we use the terminology a mean ε-representation if the group H consists of
operators."

**Theorem 5.2 (verbatim).** "Let ε > 0, let G be an amenable group, let M be a von Neumann algebra and let || · || be
a unitarily invariant, ultraweakly lower semi-continuous semi-norm || · || on M∞. Let ϕ: G → U(M) be a mean
ε-representation with respect to the metric coming from || · ||. Then there is a projection P ∈ M∞, a partial isometry
U ∈ P M∞ 1_M and a representation ρ: G → U(P M∞ P) such that ||ϕ(g) − U*ρ(g)U|| < 71ε, g ∈ G, and
||1_M − U*U|| < 40ε, ||P − UU*|| < 30ε."

**Specialization used (verbatim from the source's proof of Theorem 1.6).** "In the case M = M_n, we can identify M∞
with B(ℓ2(N)) in such a way that 1_M is a rank n projection and we use Theorem 5.2 with || · || being the 2-norm || · ||_2
coming from the semi-finite trace τ on B(ℓ2(N)) normalized in such a way that rank 1-projections have trace 1/n."
The 2-norm of a semifinite trace is unitarily invariant and ultraweakly lower semicontinuous (the source's own
example after Definition 2.4). Groups in the source are countable and discrete (abstract).

**Finite rank of P.** `U U^*` is a subprojection of `P` because `U in P M∞ 1_M` is a partial isometry, so
`P - UU^*` is a projection and `tau(P) = tau(U^*U) + ||P - UU^*||_2^2 <= 1 + 900 epsilon^2`. With rank-one
projections of trace `1/n`, `rank P < n(1 + 900 epsilon^2)`. This is the target's (DOT2).
