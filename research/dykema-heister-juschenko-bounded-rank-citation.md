---
rg: 2
id: dykema-heister-juschenko-bounded-rank-citation
kind: route
title: Import the ULIE rank computation from the published paper, read from source
target: dykema-heister-juschenko-bounded-rank-direct-finiteness
requires: []
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

Primary import.  The PDF was retrieved and read this session at
`web.ma.utexas.edu/users/juschenko/files/Dykema-Juschenko-Heister.pdf`,
dated 24 November 2014, the version published as Experimental Mathematics 24
(2015) 326--338.

Abstract, verbatim:

> "By calculating all the ULIE groups over the field `K = F_2` of two
> elements, for ranks `(3,n)`, `n <= 11` and `(5,5)`, we show that the Direct
> Finiteness Conjecture and the Invertibles Conjecture (which implies the Zero
> Divisors Conjecture) hold for these ranks over `F_2`."

Definition 2.12, read from source, fixes the semantics used in the claim:
rank is support size; the pair `(m,n)` statement quantifies over **all**
groups `G` and all `a, b` in `K[G]` of those ranks; and `m, n >= 2`.  Remark
2.13 gives the `(m,n)` / `(n,m)` symmetry.  Theorem 2.14 is the reduction that
makes the enumeration sufficient: if `K[Gamma]` is directly finite for every
`Gamma` in `ULIE_K^(-)(m,n)`, then DFC holds over `K` for the pair `(m,n)`.

What is *not* verified here: their Section 5--6 algorithm and its output.  The
`n <= 11` and `(5,5)` boundary is exactly where their computation stopped, not
where a proof stopped, so the claim should be expected to move if anyone reruns
it at larger ranks — which would raise, not lower, the floor in
`leavitt-rank-three-lift-inverse-support-thirteen`.
