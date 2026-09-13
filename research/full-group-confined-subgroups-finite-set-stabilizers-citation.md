---
rg: 2
id: full-group-confined-subgroups-finite-set-stabilizers-citation
kind: route
title: Matte Bon, Rigidity properties of full groups of pseudogroups over the Cantor set, Theorem t-confined
target: full-group-confined-subgroups-are-finite-set-stabilizers
requires: []
---

**Source.** N. Matte Bon, arXiv:1801.10133. The e-print source `hom_full_revised19.tex` was fetched and read
on MSI, 2026-09-13.

**Theorem `t-confined`** (label `t-Chabauty`, TeX line 1793, "Classification of the confined subgroups"),
verbatim: "Assume that $\mathcal{G}$ is a minimal effective étale groupoid over a space $X$ which is either
a Cantor space or a locally compact Cantor space. The following statements on a subgroup
$H\in \sub(\Ff(\G))$ are equivalent: (i) the subgroup $H$ is confined; (ii) the subgroup $H$ is confined by
$\Af(\G)$; (iii) there exists a unique finite subset ${Q}\subset X$ (possibly empty) such that we have
\[\st^0_{\Af(\G)}(Q)\le H \le \st_{\Ff(\G)}({Q}).\] Moreover let $H$ satisfy one of these equivalent
conditions, and let $P\subset \Ff(\G)\setminus \{1\}$ be a confining set. Then the set $Q$ in (iii) verifies
$|Q|\le |P|-1$."

**Definitions** (same source, introduction, subsection `s-intro-confined`, read verbatim): "A subgroup
$H\le G$ of a group $G$ is said to be \textbf{confined} if there exists a finite subset
$P\subset G\setminus \{1\}$ which intersects non-trivially all conjugates of $H$." `St^0` is used as in the
proof of Lemma `l-st-finite`, which directly follows the theorem: its elements fix a neighbourhood of `Q`
pointwise.

**The proof was read in full.** It occupies the printed region up to Corollary `c-Chabauty-G`, and has six
steps:
1. Highly minimal subdynamics.
2. The maximal proper closed invariant set `Q`.
3. `A(G|U) ≤ H` via the proximality theorem `t-proximal`.
4. Small multisections.
5. Covering (Proposition `p-nekr-cover`).
6. Uniqueness.
