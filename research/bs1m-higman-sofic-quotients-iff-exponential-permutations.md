---
rg: 2
id: bs1m-higman-sofic-quotients-iff-exponential-permutations
kind: claim
title: The cyclic Baumslag--Solitar cover has a sofic quotient keeping BS(1,m) iff order-k permutations locally multiply by m
distinct_from:
  higman-group-is-sofic: that asks whether Higman's group itself is sofic; this imports the equivalence between sofic quotients of the cover H_k(BS(1,m)) that keep BS(1,m) and exponential-like permutations of Z/nZ, for every base m.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** as a literature import through
`bs1m-higman-exponential-permutations-citation`.

**Source.** Kassabov, Kuperberg and Riley, *Soficity and variations on Higman's
group*, arXiv:1712.07191, TeX fetched on MSI on 2026-09-13. Line numbers refer
to `soficity_Higman_variations.tex`.

**Imported statements.**

1. **The cover** (l.438–442): "The semi-direct product of
   $\overline{\H}_k(G, \phi)$ with the cyclic group $C_k$ of order $k$ in which a
   generator $t$ of $C_k$ conjugates $G_i$ to $G_{i+1}$ (indices mod $k$) is
   $\H_k(G, \phi) = \langle G, t \mid t^k = 1, b^t = \phi(b); \forall b \in B \rangle$.
   Then $\overline\H_k(G, \phi)$ is the normal closure of $\iota(G)$ in
   $\H_k(G, \phi)$ and is the kernel of $\H_k(G, \phi) \to C_k$."
2. **Higman's group** (l.213): "If $G = \BS(1,2) = \langle a,b \mid b^a = b^2 \rangle$ and
   $\phi: \langle b \rangle \to \langle a \rangle$ maps $b \mapsto a$, then
   $\overline \H_4(G, \phi) = H_4$."
3. **The equivalence** (Theorem `th-functions-BS`, l.1234–1243, credited there to
   Helfgott--Juschenko): "The group $\H_k(\BS(1,m))$ has a sofic quotient $Q$
   such that the composition $\BS(1,m) \to \H_k(\BS(1,m)) \to Q$ is injective if
   and only if for all $\ep >0$ there exists an integer $C$ such that for all
   $n>C$ coprime to $m$, there exist a permutation $f \in \Sym(\Z / n \Z)$ of
   order dividing $k$ such that $f(x+1) = m f(x)$ for at least $(1-\ep)n$ values
   of $x$."
4. **Status of base two** (l.1281): "We stress that the analogue of
   Theorem~\ref{GS version} is unknown when $m=2$." Theorem `GS version`
   (l.262–266) gives the permutations with `k = 4` for all `m > 2`.

**Orientation.**
- In §`BS section` (l.1177–1195) the letters are swapped:
  `BS(1,m) = < a, b | a^b = a^m >`, with the approximations `psi_n(a) = (x -> x+1)`
  and `psi_n(b) = (x -> m^-1 x)`.
- Renaming `a <-> b`, and inverting `t` if needed (which replaces `phi` by
  `phi^-1`), identifies this cover with the one in item 2. So for `m = 2`, `k = 4`,
  the group of item 3 is `H_4 x| C_4` with `Hbar_4 = H_4`, Higman's group.

**Earlier form.** Helfgott--Juschenko, arXiv:1512.02135, Theorem 2
(`thm:jut`, l.276–288 of `Helfgott-Juschenko.tex`) proves the direction
"`H_(4,m)` sofic ⇒ such `f` with `k = 4`".
