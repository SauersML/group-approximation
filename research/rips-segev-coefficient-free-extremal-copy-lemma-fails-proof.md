---
rg: 2
id: rips-segev-coefficient-free-extremal-copy-lemma-fails-proof
kind: route
title: Place, for two or more lines of Gamma, every copy whose chosen line lies inside a long a-interval of one coset T_0; every b-edge point of every chosen line is matched by another copy of the family, so each copy meets the others in T_0 and in eight further cosets, while lines at distance three or more in Phi stay private by the shared-run corollary
target: rips-segev-coefficient-free-extremal-copy-lemma-fails
requires: [rips-segev-two-copy-configurations-carry-no-zero-divisors]
---

**Conventions.**  [TC] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`, [OC] is
`rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`, [3C] is
`rips-segev-three-copy-no-zero-divisors-proof`, [FL] is
`rips-segev-steenbock-few-line-a-supports-are-regular-proof`.  Notation as in [3C].
- Line `l` of `Gamma` is the `a`-path `v_{l,0}, ..., v_{l,C_l}`.
- `Out_l = {0, O_1, O_2, C_l}` is the set of positions that are the source of exactly one `b`-edge.
  `In_l = {0, I_1, I_2, C_l}` is the set of positions that are the target of exactly one ([OC] Conventions).
- `Phi` is the graph with one vertex per line and one edge per `b`-edge of `Gamma`.  It is 8-regular with girth
  `>= 42` ([FL] Lemma C), so it has no loops and no multiple edges.

## 1. The statement being refuted

The *coefficient-free extremal-copy lemma with threshold `t`* is the statement proposed in [3C] §6 (with `t = 3`)
and in the lane brief (with `t = 2`), read as a statement about supports only:

> (EX_t) Let `S_X, S_Y ⊆ K` be finite and port-closed: `S_X = S_Y b`.  Then every minimal covering of
> `S_X ∪ S_Y` by copies contains a copy that meets the union of the other copies of the covering in at most `t`
> links.  A link is an `<a>`-coset meeting both, or a bridge.

Port-closure is the support shadow of `X(z b) = - Y(z)`.  (EX_t) needs no coefficient input, and the lane brief
intended it to come from a Greendlinger-type count.

**Theorem.**  (EX_t) is false for every `t <= 8`.

## 2. The star family

Fix a set `L` of at least two lines, and `R >= 2 max_{l in L} C_l`.  Let `T_0 = <a>`.  For `l in L` and an integer
`s` put `h_{l,s} = a^s g(v_{l,0})^{-1}` and `C_{l,s} = h_{l,s} g(Gamma)`.  Since `g` carries `a`-edges to `a`-edges,
`h_{l,s} g(v_{l,p}) = a^{s+p}`: line `l` of `C_{l,s}` is the interval `a^{[s, s + C_l]}` of `T_0`.

The *star family* is `F = { C_{l,s} : l in L, 0 <= s, s + C_l <= R }`.  It is finite.

**Lemma 1 (distinct copies).**  Distinct pairs `(l, s)` give copies with distinct vertex sets.

*Proof.*
- If `h g(V) = h' g(V)`, then `x = h'^{-1} h` permutes the finite set `g(V)`.  Some power `x^m`, `m >= 1`, fixes
  a point, so `x^m = 1`, and `x = 1` because `K` is torsion-free.
- If `h_{l,s} = h_{l',s'}`, then `g(v_{l',0}) in g(v_{l,0}) <a>`, so the lines `l` and `l'` of `g(Gamma)` share a
  coset.  By [OC] §1 this forces `l = l'`, and then `s = s'`. ∎

**Lemma 2 (every `b`-edge point is matched).**  Let `C = C_{l,s} in F` and `d in Out_l`, and put `z = a^{s+d}`.
Then some `C' in F` with `C' != C` contains the edge `z -> z b`.  The same holds for `d in In_l` and the edge
`z b^{-1} -> z`.

*Proof.*  Pick `l' in L \ {l}` and put `p = s + d`, so `0 <= p <= R`.
- If `p + C_{l'} <= R`, take `C' = C_{l',p}`.  Its position `0 in Out_{l'}` sits at `a^p = z`.
- Otherwise `p > R - C_{l'} >= C_{l'}`.  Take `C' = C_{l', p - C_{l'}}`, which lies in `F`.  Its position
  `C_{l'} in Out_{l'}` sits at `z`.
- In both cases `C'` has the `b`-edge leaving `z`, and `C' != C` by Lemma 1.  For `In` use `0, C_{l'} in In_{l'}`
  in the same way. ∎

**Lemma 3 (nine links).**  Each `C = C_{l,s} in F` meets the union of the other members of `F` in at least 9
`<a>`-cosets: `T_0` and 8 cosets on the 8 lines of `C` adjacent to `l` in `Phi`.

*Proof.*
- Every member of `F` meets `T_0`, and `|F| >= 2`.
- Line `l` carries 8 `b`-edges of `C`: 4 leaving the positions of `Out_l` and 4 entering the positions of `In_l`.
  Their other endpoints lie on lines of `C` adjacent to `l` in `Phi`.  These 8 lines are pairwise distinct, because
  `Phi` has no multiple edges, so they lie in 8 distinct cosets ([OC] §1), all different from `T_0`.
- By Lemma 2 each of these 8 edges is also an edge of some other member of `F`.  So its far endpoint's coset
  meets that member as well. ∎

**Lemma 4 (private lines).**  Let `C = C_{l,s} in F`, and let `k` be a line at distance `>= 3` from `l` in `Phi`.
Then no other member of `F` meets the coset of line `k` of `C`, and no other member contains a vertex of that line.

*Proof.*  Suppose `C' in F \ {C}` meets that coset `T_k`.  Then `T_0` and `T_k` both lie in `S(C, C')`.  By [TC]
Corollary 3 they are joined by a `b`-run of at most 2 edges lying in `C`.  Its projection is a path of length
`<= 2` from `l` to `k` in `Phi`, which is a contradiction. ∎

Lines at distance `>= 3` exist: a ball of radius 2 in `Phi` has 65 vertices, while girth `>= 42` forces far more
vertices.

## 3. Proof of the theorem

- *The supports.*  Let `S_Y` be the set of sources of `b`-edges of members of `F`, and `S_X = S_Y b`.  These sets
  are finite and port-closed.  Every `z in S_Y` has its port edge `z -> z b` in some member, and so does every
  `x in S_X` with `x b^{-1} -> x`.  So the pattern satisfies all the support-level conclusions of [3C] Lemma 3(a).
- *Minimality.*  For `C in F`, a line `k` of `C` at `Phi`-distance `>= 3` from `l` has a vertex in `Out_k`.  That
  vertex lies in `S_Y`, and by Lemma 4 it lies in no other member of `F`.  So `F` covers `S_X ∪ S_Y` (all these
  points are vertices of members), and no proper subfamily does.
- *No extremal copy.*  By Lemma 3 every member meets the union of the others in at least 9 cosets.  Each of them
  is a link, so (EX_t) fails for `t <= 8`. ∎

## 4. What the obstruction says

- *Where it bites.*  The shell counts of `rips-segev-six-copy-no-zero-divisors-proof` use only [TC] Corollaries
  2-3 and the rank-one lemma at one pair of cosets.  The step from fixed `N` to every `N` was to come from (EX_t).
  The star family shows that support geometry alone, even with port-closure, cannot supply that step.
- *What the family violates.*  It is killed at once by the coefficients.  Each member has many clean active
  cosets (its private lines) on distinct lines, against [3C] Proposition 4(i).  So any induction on `N` must first
  impose "at most one clean active coset per copy, with at least three dirty port neighbours" (Lemma 6 of the
  six-copy proof), and only then look for an extremal copy.
- *Why stars are unavoidable.*  Around any coset of `K`, the copies containing a given point of it form a star of
  this kind.  So (EX_t) fails locally, not because of some large-scale feature of the Cayley graph.
- *Open, and the right next statement.*  The coefficient-compatible version: among port-closed patterns in which
  every copy has at most one clean active coset, some copy of a minimal covering has at most two dirty cosets.
  The star family does not satisfy the hypothesis, so it is no counterexample to this version.
- *Calibration.*  The construction uses only [OC] §1, [TC] Corollary 3, the positions `0, C_l` in both `In_l`
  and `Out_l`, and the simplicity of `Phi`.  It is valid for every Steenbock-type graph in the lane, with any
  `gamma >= 42`.
