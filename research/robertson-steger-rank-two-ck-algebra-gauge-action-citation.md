---
rg: 2
id: robertson-steger-rank-two-ck-algebra-gauge-action-citation
kind: route
title: Import of the Robertson–Steger gauge action of the torus on the rank-r Cuntz–Krieger algebra, α_t(s_{u,v}) = t^{σ(u)-σ(v)} s_{u,v}
target: robertson-steger-rank-two-ck-algebra-gauge-action
requires: []
---

**Source.** G. Robertson, T. Steger, *Affine buildings, tiling systems and higher rank
Cuntz–Krieger algebras*, J. reine angew. Math. 513 (1999), 115–144, arXiv:1302.5593.
Quoted verbatim from the arXiv TeX source `CK1.tex` (re-downloaded 2026-09-18), §"The AF
subalgebra", lines 864–872:

> Define an action $\alpha$ of the $r$-torus $\TT^r$ on $\cA$ as follows.
> If $\s(u)-\s(v) =m \in \ZZ^r$ and $t=(t_1,\dots,t_r) \in \TT^r$,
> let $\alpha_t(s_{u,v}) = t^ms_{u,v}$, where $t^m=t_1^{m_1}t_2^{m_2}\dots t_r^{m_r}$.
> The elements $\alpha_t(s_{u,v})$ satisfy the relations (\ref{rel1})
> and generate the $C^*$-algebra $\cA$. By the universal property of $\cA$
> it follows that $\alpha_t$ extends to an automorphism
> of $\cA$. It is easy to see that that $t\mapsto \alpha_t$ is an action.
> It is also clear that $\alpha_t$ fixes all elements $s_{u,v}$ with $\s(u)=\s(v)$
> and so fixes $\cF$ pointwise.

Standing hypotheses at that point (line 634): "Assume conditions (H0)-(H3) hold." Here
`\s` is the shape `σ`, `\cA` is the C\*-algebra `𝒜` with generators `s_{u,v}`,
`u, v ∈ W̄`, `t(u) = t(v)`, defined by the relations (rel1) (lines 655–683, imported in
`robertson-steger-boundary-cylinders-and-pure-infiniteness`, item 1), and `\cF` is the
AF subalgebra.

**Why the hypotheses hold in the Ã₂ setting.** For a type rotating group `Γ` acting freely
on the vertices of a locally finite thick Ã₂ building with finitely many vertex orbits,
(H0), (H1), (H3) hold by Proposition `M_1M_2`, and (H2) holds when the building is that of
`PGL_3(K)`, `K` nonarchimedean of characteristic zero, and `Γ` is a lattice (both imported
in `robertson-steger-a2-boundary-algebras-are-rank-two-ck`). There `r = 2`.

**Check of the claim sentence "the elements α_t(s_{u,v}) satisfy the relations".** The
check is immediate and recorded only for the referee. With `n(u,v) = σ(u) - σ(v)`:
- (rel1a): `n(v,u) = -n(u,v)` and `conj(t^m) = t^{-m}` on the torus;
- (rel1b): `n(u,v) + n(v,w) = n(u,w)`;
- (rel1c): `n(uw,vw) = n(u,v)`, because `σ(uw) = σ(u) + σ(w)`;
- (rel1d): `n(u,u) = 0`.
