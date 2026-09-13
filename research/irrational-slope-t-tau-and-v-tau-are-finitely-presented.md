---
rg: 2
id: irrational-slope-t-tau-and-v-tau-are-finitely-presented
kind: claim
title: The irrational-slope Thompson groups T_τ and V_τ are finitely presented
distinct_from:
  pl-rearrangement-groups-have-two-transitive-orbit-actions: that proves the orbit action of V(A,P) is of type (A) exactly when V(A,P) is finitely presented; this is the finite presentation itself for A = Z[τ] and P = <τ>.
---

**OPEN (as a graph node).** Let `τ = (√5 − 1)/2`. The groups `T_τ` (piecewise-linear
orientation-preserving homeomorphisms of the circle with breakpoints in `Z[τ]` and
slopes powers of `τ`) and `V_τ` (the analogous left-continuous piecewise-linear
bijections of `(0,1]`) are finitely presented.

## Literature (read from the arXiv TeX on MSI)

- **Burillo--Nucinkis--Reeves, arXiv:2006.02401**, `ttau.tex` l.101:
  "Also note that these groups are of type $F_\infty.$ The result for $\ft$ was proven
  in \cite{clearyirr}, see \cite{clearyirrold} for detail. The extension of the result
  to $\ttt$ and $\vt$ follows by directly applying the methods of Stein \cite{stein}.
  These methods are by now standard, see, for example, \cite{FMWZ, KoMN4, MMN}, and we
  will not present them here."
- The definitions, l.111: "the group \ttt\ is the group of piecewise-linear,
  orientation-preserving homeomorphisms of the circle such that the breakpoints are in
  $\zz[\tau]$ and the slopes of the linear parts are powers of $\tau$. The $V$-version
  \vt\ consists of the left-continuous, piecewise-linear maps of $(0,1]$, also with
  breaks in $\zz[\tau]$ and slopes powers of $\tau$."
- For `F_τ` the statement is Cleary's theorem, as quoted by Burillo--Nucinkis--Reeves,
  arXiv:1806.00108, l.137: "Cleary proved that the group is of type $F_\infty$, so in
  particular, it is finitely presented".

## Why this node is OPEN

The type `F_∞` statement for `T_τ` and `V_τ` is asserted with its proof deferred to
"the methods of Stein". No written proof was found or checked here, so it is recorded
as the published assertion it is and not imported as ESTABLISHED. A proof along the
Stein--Farley or Brown-criterion lines, or a citation to a written one, would close it.

## Consequence waiting on it

`irrational-slope-v-tau-subgroups-satisfy-pbh`, through
`irrational-slope-v-tau-pbh-via-orbit-action`.
