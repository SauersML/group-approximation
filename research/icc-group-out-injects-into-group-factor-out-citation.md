---
rg: 2
id: icc-group-out-injects-into-group-factor-out-citation
kind: route
title: Import Proposition inj of Chifan–Ioana–Osin–Sun II, read at source
target: icc-group-out-injects-into-group-factor-out
requires: []
artifacts:
  - research/artifacts/sk-vn-rigidity-2026-09-14.md
---

Read on MSI 2026-09-14 from the arXiv e-print of arXiv:2304.07457 (file `main`).

**l.220, verbatim.**
> which is neither injective, nor surjective in general.  If $G$ satisfies the ICC condition, the injectivity of this map is not difficult to prove (see Proposition \ref{inj} and Remark \ref{RemFin}).

**l.2048, Proposition `inj`, verbatim.**
> If $G$ is ICC, then $\overline{\Psi}$ is injective.

**Proof in the source (l.2053–2059), summary.**
- If `Ψ_{ρ,δ} = Ad(u)` with `u = Σ c_h u_h`, then comparing Fourier coefficients gives `ρ(g)c_h = c_{δ(g)hg^{-1}}`.
- So `|c_h|` is constant on the twisted conjugacy classes `{δ(g)hg^{-1}}`, and `Σ|c_h|^2 = 1` forces some class to be finite.
- A finite-index subgroup `G_h` then satisfies `δ(g) = hgh^{-1}` on `G_h`, and ICC upgrades this to all of `G`.

**Remark `RemFin` (l.2066–2071), summary.** ICC is necessary: Burnside's class-preserving outer automorphisms of finite groups
induce inner automorphisms of `L(K) = CK`.

Not checked: the journal numbering of the proposition (Duke Math. J. 175 (2026)).
