---
rg: 2
id: labeled-oriented-trees-are-aspherical
kind: claim
title: Every labeled oriented tree complex is aspherical
distinct_from:
  whitehead-asphericity-conjecture: that is the general statement about connected subcomplexes of aspherical 2-complexes; this is the special case of LOT complexes, which the Whitehead conjecture implies and which Howie's reduction ties back to the finite case up to Andrews--Curtis moves.
  injective-labeled-oriented-trees-are-aspherical: that is the established injective case; this asks for all labeled oriented trees, including those in which a vertex labels several edges.
---

**OPEN.** A labeled oriented tree (LOT) is a tree whose oriented edges
`e = [s, l, t]` (from `s` to `t`) are labeled by vertices `l`. Its LOT
presentation has one generator per vertex and one relator `s l t^-1 l^-1` per
edge, and `K(Γ)` is the standard 2-complex. The claim: `K(Γ)` is aspherical for
every LOT `Γ`.

Why it matters (arXiv:1212.1943 l.98): "Howie showed that the finite case of the
Whitehead conjecture reduces, up to the Andrews-Curtis conjecture, to the
statement that presentations arising from labeled oriented trees are aspherical."
Conversely `lot-asphericity-via-whitehead-conjecture` shows the Whitehead
conjecture implies this claim, so a non-aspherical LOT would refute Whitehead.

Status at source (arXiv:2207.07991, Harlander--Rosebrock 2022, l.102):
"Asphericity, known for classical knots, is unresolved for LOTs. The asphericity
question for LOTs is of central importance to Whitehead's asphericity
conjecture". LOT complexes are spines of ribbon 2-knot complements (same line,
citing Howie 1983).

Known aspherical classes recorded on main: injective LOTs, LOTs whose `T(Γ)` or
`I(Γ)` has no cycles, deforestable LOTs, LOTs passing the coloring test, and
the two relative constructions through maximal sub-LOTs (see `requires` of the
routes into the census node).

## Attempts

1. *Exhaustive census of small reduced LOTs* (lane hl-whitehead-relative,
   2026-09-13): every reduced LOT up to a vertex bound is run through the
   published certificates above; see
   `reduced-labeled-oriented-trees-small-census-aspherical` for what is proved
   and which LOTs remain uncertified.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
