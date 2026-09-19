---
rg: 2
id: lifted-thompson-t-template-envelope-contains-shift-graphs
kind: claim
title: "Conjugate-template codes in T-bar see only line digraphs of conjugation orbitals, and an explicit Thompson-F template on the triple shift graph passes every test except relator area"
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that is the sufficient criterion (bounded-area code on an infinite-chromatic graph kills its mark); this describes the graphs a conjugate template can carry in T-bar and builds one on an infinite-chromatic graph with exact commutation, leaving only the area bound.
  lifted-thompson-t-is-not-mf: that is the target; this is a structural statement about one class of attacks on it and proves nothing about MF.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-template-envelope-shift-graph-proof`.

## Setting

`Gamma` is a group (below, the lifted Thompson group `T̄`, or its subgroup
`F`, lifted as the maps fixing `Z` and commuting with `z`).  A *conjugate
template* with mark `x = [c,h] != 1` on an oriented graph `G` is a choice of
word `u_v` for each vertex `v` with

```text
C_v = u_v c u_v^(-1),   H_v = u_v h u_v^(-1),   a_v = u_v,
```

so that `[C_v,H_v] = a_v x a_v^(-1)` holds freely (CCC1 with area 0).
It is a *code* when (CCC2) holds: `Area([C_w,H_v]) <= A_0` on every oriented
edge `(v,w)`.  By `infinite-chromatic-commutator-code-kills-mf-mark` a code
on a graph with `chi(G) = infinity` kills `x` in every corona model.

The wave-18 lane (swarm branch, node
`lifted-thompson-t-conjugate-template-codes-have-bounded-cliques`) showed,
by annular localization, that every code edge satisfies the
*element-level condition*

```text
k := g_v^(-1) g_w  lies in  S(F,F_1) := { k : [kck^(-1),h] = 1,
                                          kck^(-1) in F,  k^(-1)hk in F_1 }   (N)
```

for finite sets `F, F_1` depending on `c, h, A_0` only (`g_v` is the
element of `u_v`).  It concluded bounded cliques and left "shift-graph-like"
templates open.

## Statement

**1. (Envelope = line digraphs of orbitals.)**  For any group `Gamma`, any
`c, h` with `[c,h] != 1` and any finite `F, F_1`, let
`Y = Cay(Gamma, S(F,F_1))` (arcs `g -> gk`).  Then:

- `S(F,F_1)` is a union of at most `|F||F_1|` left cosets `s_i D_i`, with
  `D_i = C(c) ∩ C(f_i)`, where `f_i = s_i^(-1) h s_i` commutes with `c`.
- `Cay(Gamma, s D)` is *exactly* the line digraph `L(Z)` of the multidigraph
  `Z = Z(Gamma; D, s)` on `Gamma/D` having one arc `gD -> gsD` for each
  `g in Gamma`.  Its underlying simple digraph is the orbital digraph of
  the pair `(P, sP)` under conjugation, where `P = (c, f_i)` and
  `Gamma/D` is identified with the conjugation orbit of `P`.  `Z` has no
  loops.
- Consequently every conjugate template satisfying (N) has
  `chi(G) <= prod_i chi(L(Z_i))`, and
  `log_2 chi(Z_i) <= chi(L(Z_i)) <= min{k : chi(Z_i) <= binom(k, floor(k/2))}`.
  Each `L(Z_i)` has undirected clique number at most 3.
- If `[D_i : D_i ∩ s_i D_i s_i^(-1)] <= m` for all `i` (or the same with
  `s_i^(-1)`), then `chi(Z_i) <= 2m+1`, so **every** conjugate template
  satisfying (N) has finite chromatic number and dies.

So, at the element level, the conjugate-template survivors are exactly the
line digraphs of infinite-chromatic orbital digraphs of commuting pairs.
They need non-commensurated centralizer intersections `D_i`.

**2. (The envelope is infinite-chromatic in Thompson's F.)**  Take standard
dyadic intervals

```text
I = [5/16, 3/8],  K = [3/4, 7/8],  sI = [1/16, 1/8],  sK = [1/4, 1/2],
E_j = [2^(-2j-2), 2^(-2j-1)],  alpha_j = 2^(-2j) I   (j >= 1).
```

Let `c_J` denote the affine transport of `x_0` into the standard dyadic
interval `J`.  Put `c = c_I` and `h = c_{sK}`, and let `s in F` be affine
from `I` onto `sI` and from `K` onto `sK`.  For `i < j < l`, choose
`t_{ijl} in F` affine from `sI` onto `alpha_l`, from `sK` onto `E_j`, and
from `K` onto `E_i`, and let `u_{ijl}` be any word for it.  Then on the
triple shift graph `Sh_3(N)` (arcs `(i,j,l) -> (j,l,m)`):

- the mark `x = [c,h] != 1` and CCC1 holds with area 0;
- every edge commutes **exactly**: `[C_w, H_v] = [c_{alpha_l}, c_{E_j}] = 1`;
- every edge satisfies (N) with the one-point sets `F = {c_{sI}}` and
  `F_1 = {c_K}`: `k c k^(-1) = c_{sI}` and `k^(-1) h k = c_K`;
- `chi(Sh_3(N)) = infinity` (Erdős–Hajnal), while `omega = 2`.

Hence **no argument that uses only element-level data can kill conjugate
templates in `T̄`**.  Such data include localization, translation numbers,
slope spectra, the conclusion (N), and exact commutation.  The survivor
class of w18 is not empty below the area level.  It has an explicit
member, which lives in `F`.

## What this changes

- **Class kill (precise obstruction).**  Consider the approach "finish off
  conjugate templates in `T̄` with invariants of the group elements".  It
  dies at item 2.  The invariant is the pair of supports modulo affine
  transport.  The death step: that invariant is realised by a shift-graph
  configuration of disjoint dyadic intervals.  Any kill must use the
  *words* `u_v`, meaning the growth of `Area([C_w,H_v])` along the table.
- **Decomposition of what remains.**  Every conjugate-template code in
  `T̄` lives in some `L(Z_i)` with `Z_i` infinite-chromatic.  The explicit
  data of item 2 yield a code, and so a proof that `x` dies in every MF
  model of `T̄`, if and only if there are words `u_{ijl}` with

  ```text
  sup over arcs (i,j,l)->(j,l,m) of  Area([k c k^(-1), h]) < infinity,
  k = u_{ijl}^(-1) u_{jlm},  whose element is s·d with d in C(c) ∩ C(c_K)
  ```

  Here `d` fixes `I ∪ K` pointwise and takes infinitely many values.  That is one
  concrete Dehn-function question in `T̄`.  A negative answer for all
  words is the only way left to kill this template.  The metric-agnostic
  code theorem (swarm node `chromatic-mark-codes-are-metric-agnostic`)
  would make a positive answer prove `T̄` non-hyperlinear.  If the area
  were bounded already in a finite presentation of `F`, it would also prove
  `F` non-hyperlinear, and hence non-amenable.  So the belief is that the
  area is unbounded, but nothing in the graph proves it.  The natural tool
  is a thin-diagram (bridge) count.  At most `A_0 M` boundary letters of a
  diagram for `[kck^(-1),h]` touch 2-cells.  The rest pair up by
  non-crossing free cancellation, so long runs of the four `k`-segments must
  cancel against each other.  One then needs to show that the family `k`
  is incompatible with that pairing.  The w17 lane did this for the literal
  shift words `x_0^n`.
- **Consistency.**  `Sh_3(N)` is triangle-free.  This agrees with the w18
  clique bound, and it shows that the clique bound cannot be upgraded to a
  chromatic bound.
