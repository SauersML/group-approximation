---
rg: 2
id: fp-groups-without-free-subgroups-ascending-splitting-citation
kind: route
title: Import Cornulier–de la Harpe Corollary 8.C.4 and the ascending-HNN remark
target: fp-groups-without-free-subgroups-split-ascendingly-over-kernels
requires: []
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
---

Citation import, secondary source. Read 2026-09-13 from the TeX source of Y. Cornulier and
P. de la Harpe, *Metric geometry of locally compact groups*, arXiv:1403.3796 (`main.tex`,
fetched on MSI). Line numbers refer to that file. The original is R. Bieri and R. Strebel,
Comment. Math. Helv. 53 (1978), Theorem A, which was not re-read.

**Definition 8.C.1 (l.19058–19101), verbatim excerpt.**
"Let $G$ be a group, $H$ a subgroup, and $\pi : G \twoheadrightarrow \Z$ an epimorphism. We
say that $\pi$ \textbf{splits over $H$}, or has a \textbf{splitting over $H$}, if (1)
$H \subset \ker (\pi)$ and there exist splitting data, namely: (2) an element, called the
\textbf{stable letter}, $s \in \pi^{-1}(\{1\}) \subset G$ ; (3) two subgroups $K,L$ of $H$ such
that $L = sKs^{-1}$ ; (4) an isomorphism
$\psi : \HNN(H,K,L,\varphi) = \langle H,t \mid t k t^{-1} = \varphi (k) \text{ for all } k \in K \rangle \overset{\simeq}{\longrightarrow} G$,
where $\varphi$ is the isomorphism of $K$ onto $L$ defined by $\varphi(k) = s k s^{-1}$, such
that the restriction of $\psi$ to $H$ is the identity, and $\psi (t) = s$. The splitting is
\textbf{ascending} if at least one of $K=H$, $L=H$ holds, \textbf{essential} if $K \ne H \ne L$."

**Corollary 8.C.4 (l.19199–19209), verbatim.**
"Let $G$ be a compactly presented LC-group. Suppose that the free group of rank $2$ does not
embed as a discrete subgroup of $G$. For every continuous epimorphism
$\pi : G \twoheadrightarrow \Z$, either $\pi$ or $-\pi$ splits ascendingly over some compactly
generated open subgroup."

**Remark 8.B, item (5) (l.18964–18971), verbatim excerpt.**
"Let $G$ be an LC-group that is an ascending HNN-extension; we use the notation of Proposition
\ref{topHNN}. Then $N := \bigcup_{n \ge 1} t^{-n}Ht^n$ is an open normal subgroup of $G$, and
$G/N \simeq \Z$."

**Specialization.**
- **Discrete setting.** A discrete group is compactly presented exactly when it is finitely
  presented. A subgroup is compactly generated and open exactly when it is finitely
  generated. Every subgroup of a discrete group is discrete.
- **Taking the ascending splitting.** Take the ascending splitting of `eps*pi` over `H`,
  with stable letter `s` (`eps*pi(s) = 1`). Then `H <= ker(pi)`.
- **Case `K = H`.** Here `s H s^-1 <= H`, so `H <= s^-1 H s`, and the union `N` of the
  remark increases. `N` is normal, lies in `ker(pi)`, and has `G/N ≅ Z`. So `pi` induces a
  surjection `Z -> Z`, hence an isomorphism, and `N = ker(pi)`.
- **Case `L = H`.** The same argument applies with `s^-1` in place of `s`.
