---
rg: 2
id: kazhdan-host-route-imports-citation
kind: route
title: Import Higson-Roe via Willett's notes and Chatterji-Drutu-Haglund's kernel theorem, then metrize the amenable model by coordinates
target: kazhdan-host-route-imports-have-verbatim-sources
requires: []
---

Written by referee ref-03 (2026-09-17). Source texts were fetched from arXiv and read at
the quoted lines.

## Item 1: property A gives a compact metrizable amenable model in form (R1)

**Source.** R. Willett, *Some notes on Property A*, arXiv:math/0612492v2 (source file
`PropertyA.tex`, fetched 2026-09-17). Groups carry a bounded geometry left-invariant
metric (l.1544–1595), so the closed balls `B̄(e,R)` are finite and exhaust the group.
Verbatim:

- Definition, l.4115–4124: "A (countable discrete) group $G$ is said to act
  \emph{topologically amenably} on the compact Hausdorff space $X$ if for all
  $R,\epsilon>0$ there exists a weak-$*$ continuous map $\xi:X\to{}l^1(G)$ such that
  \begin{enumerate} \item $\|\xi_x\|_1=1$ for all $x\in{}X$; \item for all
  $g\in\bar{B}(e,R)$ and all $x\in{}X$, $\|g\xi_x-\xi_{gx}\|_1<\epsilon$."
- Theorem, l.4246–4249, attributed to Higson–Roe [HR00a, 1.1]: "A countable discrete
  group $G$ has property A if and only if it admits an amenable action on some compact
  Hausdorff space."

The notion of property A there is Yu's (l.449–450, "\begin{propa}[Property A, \cite{y1}]"), the same
notion Guentner–Tessera–Yu supply in `commutative-ring-linear-groups-have-property-a`.

**Upgrade to (R1) on a metrizable space.** Let `Γ` be countable with property A, acting
amenably on a compact Hausdorff `X` as above.

1. For each `n` take `ξ^n` for `(R, ε) = (n, 1/n)` and put `μ_n(x) = |ξ^n_x|`
   (pointwise absolute value). Then `μ_n(x) ∈ Prob(Γ)`, since `||ξ^n_x||_1 = 1`.
   Each coordinate `x ↦ μ_n(x)(η)` is continuous, because evaluation at `η` is
   weak-* continuous on `l^1(Γ)` and `|·|` is continuous. Also
   `||γμ_n(x) − μ_n(γx)||_1 = || |γξ^n_x| − |ξ^n_{γx}| ||_1 ≤ ||γξ^n_x − ξ^n_{γx}||_1`.
   So for every `γ`, `sup_x ||γμ_n(x) − μ_n(γx)||_1 < 1/n` once `γ ∈ B̄(e,n)`.
2. Let `F = {f_{n,η} : x ↦ μ_n(x)(η)}`, a countable set of functions `X → [0,1]`.
   Define `q: X → [0,1]^{F × Γ}` by `q(x)_{f,g} = f(gx)`. It is continuous. Its image
   `Y = q(X)` is compact and metrizable, being inside a countable product.
3. `Γ` acts continuously on `[0,1]^{F×Γ}` by `(δ·t)_{f,g} = t_{f,gδ}`. This is an
   action: `(δ'·(δ·t))_{f,g} = (δ·t)_{f,gδ'} = t_{f,gδ'δ}`. And `q` is equivariant:
   `q(δx)_{f,g} = f(gδx) = q(x)_{f,gδ} = (δ·q(x))_{f,g}`. So `Y` is invariant.
4. Put `ν_n(y)(η) = y_{f_{n,η}, e}`. Then `ν_n(q(x)) = μ_n(x)`. Since `q` is onto `Y`,
   every `ν_n(y)` is a probability measure, each coordinate of `ν_n` is continuous, and
   `sup_{y∈Y} ||γν_n(y) − ν_n(γy)||_1 = sup_{x∈X} ||γμ_n(x) − μ_n(γx)||_1`, because
   `ν_n(γq(x)) = ν_n(q(γx)) = μ_n(γx)`.

So `Γ ↷ Y` is a continuous action on a compact metrizable space with continuous
`ν_n: Y → Prob(Γ)` satisfying, for each `γ`, `sup_y ||γν_n(y) − ν_n(γy)||_1 → 0`. This is
form (R1), and Step 0 of `amenable-purely-infinite-groupoid-kazhdan-host-proof` uses only
this (coordinatewise continuity and the uniform estimate). Item 1 holds.

## Item 2: (T) plus Haagerup is finite

**Source.** I. Chatterji, C. Druţu, F. Haglund, *Kazhdan and Haagerup properties from the
median viewpoint*, Adv. Math. 225 (2010), arXiv:0704.3749 (source file
`MediAnalyse-final.tex`, fetched 2026-09-17), Theorem `THker`, l.2519–2529, verbatim:

> \begin{thm}[\cite{Delorme}, \cite{Guichardet}, \cite{AkermannWalter},
> \cite{delaHarpeValette:proprieteT}, \cite{CCJJV}]\label{THker} Let $G$ be a second
> countable, locally compact group. \begin{enumerate} \item The group $G$ has property
> (T) if and only if every continuous conditionally negative definite function on $G$ is
> bounded (equivalently, every continuous left invariant conditionally negative definite
> kernel on $G$ is bounded). \item The group $G$ has the Haagerup property if and only if
> there exists a continuous proper conditionally negative definite function on $G$
> (equivalently, there exists a continuous proper left invariant conditionally negative
> definite kernel on $G$). \end{enumerate} \end{thm}

A countable discrete group is second countable and locally compact, and every function on
it is continuous. Suppose `Λ` is countable with property (T) and the Haagerup property. By
(2) there is a proper conditionally negative definite `ψ` on `Λ`. By (1), `ψ ≤ c` for some
`c`. Properness says `{λ : ψ(λ) ≤ c}` is finite, and this set is `Λ`. So `Λ` is finite.

Passage to subgroups, as used in the host route: if `L ≤ Λ` and `ψ` is a proper
conditionally negative definite function on `Λ`, then `ψ|_L` is conditionally negative
definite (the defining inequalities only involve finitely many group elements and their
quotients, all in `L`) and proper (`{l : ψ(l) ≤ c} = L ∩ {λ : ψ(λ) ≤ c}`). So by (2) the
Haagerup property passes to subgroups. Item 2 holds.
