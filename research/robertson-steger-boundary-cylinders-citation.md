---
rg: 2
id: robertson-steger-boundary-cylinders-citation
kind: route
title: Import of Robertson–Steger 1999, relations (rel1), the formula for φ, Lemmas c1 and c2, the proof of main2, and the remark after it
target: robertson-steger-boundary-cylinders-and-pure-infiniteness
requires: []
---

**Source.** G. Robertson, T. Steger, *Affine buildings, tiling systems and higher rank
Cuntz–Krieger algebras*, J. reine angew. Math. 513 (1999), 115–144, arXiv:1302.5593.

**How it was read.** The arXiv e-print TeX was fetched on 2026-09-17. Line numbers below
refer to that file. Quotes are verbatim TeX.

**Verbatim.**

- l.660–677, generators and defining relations:
  "The generators of $\cA$ are therefore
  \{s_{u,v};\ u,v \in \overline W \ \text{and} \ t(u) = t(v) \}
  and the defining relations are
  {s_{u,v}}^* = s_{v,u} ;
  s_{u,v}s_{v,w} = s_{u,w} ;
  s_{u,v} = \sum_{w\in W;\s(w)=e_j, o(w)=t(u)=t(v)} s_{uw,vw} ,\ \text{for} \ 1 \le j \le r ;
  s_{u,u}s_{v,v} = 0 \ \text{for} \ u,v \in \overline W_0, u \ne v ."
- Corollary `4`, l.461–467: "If $\overline u=(d,u) \in \overline W_m$ and $v \in W_n$
  with $t(\ou) = o(v)$, then there exists a unique $\ow \in \overline W_{m+n}$ such that
  $$\ow\vert_{[0,m]}=\ou \ \text{and} \ \ow\vert_{[m,m+n]}=v.$$ In these circumstances we
  write $\ow =\ou v$, and say that the product $\ou v$ exists."
- Lemma `f2`, l.684–693: "Fix $m \in \ZZ^r_+$ and let $u,v \in \overline W$ with $t(u) =
  t(v)$. Then $s_{u,v}= \sum_{w\in W;\s(w)=m, o(w)=t(u)=t(v)} s_{uw,vw}$."
- Lemma `5`, l.699: "$s_{u,u}s_{v,v}=0$ if $\s(u)=\s(v)$ and $u \ne v$."
- l.1749–1750: "Let $\ofW_m$ denote the set of type rotating isometries
  $p :\fp_m \to \cB$ such that $p(0,0)=O$ and let $\ofW = \bigcup_m \ofW_m$."
- Lemma `oalpha`, l.1759–1761: "The map $\oa$ is a bijection from $\ofW_m$ onto
  $\oW_m$ for each $m \in \ZZ^2_+$."
- l.1778–1782: "$\Omega(p)=\Omega(p(m_1+1,m_2+1)) = \left \{ \omega \in \Omega ; t(p)
  \subset [O,\omega) \right \} =\left \{ \omega \in \Omega ; p(\fp_m) \subset [O,\omega)
  \right \}$."
- l.1794–1800: "Fix $\ow_1, \ow_2 \in \oW$ with $t(\ow_1)=t(\ow_2)=a \in A$. Let
  $p_1=\oa^{-1}(\ow_1)$ and $p_2=\oa^{-1}(\ow_2)$. Let $\g \in \G$ be the unique element
  such that $\g t(p_1)=t(p_2)$. Define a homomorphism $\phi: \cA \to C(\Om)\rtimes \G$ by
  $\phi(s_{\ow_2,\ow_1})=\g \Ind _{\Om(p_1)}= \Ind _{\Om(p_2)}\g$."
- Lemma `c1`, l.1809–1811: "For any $m \in \ZZ^2_+$, $\Ind = \displaystyle \sum_{p \in
  \ofW_m} \Ind _ {\Omega(p)}$."
- Lemma `c2`, proof, l.1822–1823: "the sets $\Omega(p)$ for $p \in \ofW$ form a basis for
  the topology of $\Om$."
- Theorem `main2`, proof, l.1910–1916: "If $p \in \oW$ then
  $\Ind _{\Omega(p)}=\phi(s_{\ow,\ow})$, where $\ow=\oa(p)$ [...] Fix $\g \in \G$. Choose
  $m=(m_1,m_2)$ so that $d(O,\g^{-1}O) \le m_1, m_2$. Now $\g = \g \Ind =
  \displaystyle \sum_{p \in \ofW_m} \g \Ind _ {\Omega(p)}$. For $p \in \ofW_m$ we claim
  that $\g t(p) = t(p')$ for some $p' \in \ofW$. Hence $\g \Ind _ {\Omega(p)} = \phi
  \left(s_{\alpha(p'),\alpha(p)}\right)$."
  - Here `\alpha(p)` in the last display is `\oa(p)`, as the preceding line and the
    definition at l.1794–1800 show.
  - The claim is proved at l.1919–1922 through Corollary `9B`.
- Remark after `main2`, l.1925–1932: "It follows from Theorem~\ref{main2} and
  Remark~\ref{previous} that $C(\Om)\rtimes \G$ is simple, nuclear and purely infinite.
  [...] From simplicity it follows that $C(\Om)\rtimes\G$ is isomorphic to the reduced
  crossed product $C(\Om)\rtimes_r \G$."
- l.1940–1948: "assuming throughout that $\G$~acts on~$\cB$ via type rotating
  automorphisms. We prove that conditions (H0), (H1), and (H3) are satisfied so long as
  $\G$~acts freely and with finitely many orbits on the vertices of~$\cB$. Moreover, if
  $\cB$ is the building of $G=\PGL_3(\KK)$, where $\KK$ is a nonarchimedean local field of
  characteristic zero and $\G$ is a lattice in $\PGL_3(\KK)$ we prove that (H2) holds as
  well. There are several concrete examples in \cite{cmsz} where all these hypotheses are
  satisfied."

**Hypothesis match.** Every downstream use is for a lattice `Γ` in `PGL_3(K)`, with `K`
nonarchimedean of characteristic zero, acting freely and type rotatingly on the vertices
with finitely many orbits. That is the setting of l.1940–1948, where (H0)–(H3) all hold.
Theorem `main2` and the remark after it are proved under these hypotheses.
