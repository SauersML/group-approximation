---
rg: 2
id: abc-leavitt-kh-vanishing-and-nil-splitting-citation
kind: route
title: Import ABC arXiv:0903.0056 Theorem 5.10, Theorem 8.6, the Section 5 description of L_0 and φ, and the Section 8 K_n-regularity comparison (Weibel), and specialise to the rose with two petals
target: leavitt-tensor-k-theory-is-pure-twisted-nil
requires: []
artifacts:
  - experiments/leavitt-kh-2026-09-17/abc-0903.0056-excerpts.txt
---

**Citation import.** P. Ara, M. Brustenga and G. Cortiñas, *K-theory of Leavitt
path algebras*, Münster J. Math. 2 (2009) 5–33, arXiv:0903.0056. The text was
read on 2026-09-18 from https://arxiv.org/html/0903.0056. The artifact
`experiments/leavitt-kh-2026-09-17/abc-0903.0056-excerpts.txt` stores the
extracted passages verbatim, with math given as its TeX source.

- **Theorem 5.10.** "Let $A$ be an $H^{\prime}$-unital ring, $E$ a finite
  quiver, $M=M_{E}$ and $N=N_{E}$. Assume the quiver $E$ has no sources. We have
  $K(L_{A}(E))\cong NK(L_{0}\otimes A,\phi\otimes 1)_{+}\oplus NK(L_{0}\otimes A,\phi\otimes 1)_{-}\oplus\cofi(K(A)^{e_{0}-e_{0}^{\prime}}\overset{1-N^{t}}{\longrightarrow}K(A)^{e_{0}})$."
  The text before the theorem says: "Let $e_{0}^{\prime}=|{\rm Sink}(E)|$",
  "By a slight abuse of notation, we will write $1-N_{E}^{t}$ for this matrix",
  and "Of course $N_{E}=N_{E}^{\prime}$ in case $E$ has no sinks". Here `e_0` is
  the number of vertices, because `K(A)^(e_0)` is indexed by `E_0`.
- **Theorem 8.6.** "Let $A$ be a ring, and $E$ a row-finite quiver. Then
  $KH(L_{A}(E))\cong\cofi(KH(A)^{(E_{0}\setminus{\rm Sink}(E))}\overset{1-N_{E}^{t}}{\longrightarrow}KH(A)^{(E_{0})})$."
- **Section 8, comparison map (8.1) `K_*(A) -> KH_*(A)`.** "It is proved in
  [32] that if $A$ is unital and $K_{n}(A)\to K_{n}(A[t_{1},\dots,t_{p}])$ is an
  isomorphism for all $p\geq 1$ (i.e. $A$ is $K_{n}$-regular) then (8.1) is an
  isomorphism for $*\leq n$."
  - Reference [32] is: "C. Weibel. Homotopy Algebraic $K$-theory. Contemporary
    Math. 83 (1989)".
- **Section 2.** "Unital rings are both $H$ and $H^{\prime}$-unital."
- **Section 5.**
  - "the ring $L_{0,n}$ is isomorphic to
    $\big[\prod_{m=0}^{n-1}\big(\prod_{i\in{\rm Sink}(E)}M_{|P(m,i)|}(\mathbb{Z})\big)\big]\times\big[\prod_{i\in E_{0}}M_{|P(n,i)|}(\mathbb{Z})\big]$".
  - "$P(n,i)$ the set of paths $\gamma$ in $E$ such that $|\gamma|=n$ and
    $r(\gamma)=i$".
  - "$\phi:L\to L,\qquad\phi(x)=t_{+}xt_{-}$".
  - "$L=L_{0}[t_{+},t_{-},\phi].$"
  - "$L_{A}(E)=L_{\mathbb{Z}}(E)\otimes A.$ (5.9) If $A$ is a not necessarily
    unital ring, we take (5.9) as the definition of $L_{A}(E)$."

**Specialisation, checked in the target.** Take `E = R_2`, with one vertex and
two loops. Then:
- `E` is finite and row-finite, and has no sinks and no sources;
- `N_E^t = (2)` and `1 - N_E^t = -1`;
- `|P(n,v)| = 2^n`.

No proof is re-derived beyond this arithmetic.

**Trust surface.**
- The comparison statement is ABC's report of Weibel [32]. Weibel's paper
  itself was not re-read. ABC state it for unital `A`, and it is applied here
  only to unital `A ⊗ L`.
- Theorem 8.6's proof, as quoted in the artifact, reduces to ABC Theorem 8.4
  and the method of Theorem 5.10. It was not re-checked.
