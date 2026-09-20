---
rg: 2
id: fpbs-price-one-forests-have-infinitely-many-components
kind: claim
title: On a nonamenable group of minimal cost one, every invariant random spanning forest has infinitely many components
distinct_from:
  fpbs-universal-priority-deletion-connected-fmsf: that builds a connected invariant subgraph H containing the FMSF and says nothing about the number of FMSF components; this proves the FMSF, and every invariant spanning forest, has infinitely many components on the whole open class
  fpbs-msf-excess-equals-nonuniqueness: that identifies p_c<p_u with FMSF degree excess delta_G>0; this is about the number of components of an invariant forest, and it gives the cost formula C_*=1+(E deg/2-1)/k for k components
  gaboriau-treeable-free-action-realizes-min-cost: that is the imported cost theory for treeings; this applies it to a coset lift of an invariant forest with finitely many components
  fpbs-fusf-not-connected-on-some-cayley-graphs: that cites disconnection of the FUSF on some virtually free Cayley graphs; this proves infinitely many components for every invariant forest on every Cayley graph of every nonamenable group with C_*=1
  fpbs-wired-forest-degree-two: that builds a wired forest inside a connected invariant subgraph; this bounds the component count of any invariant spanning forest from the minimal cost of the group
---

**ESTABLISHED.** Proof route: `fpbs-price-one-forests-have-infinitely-many-components-proof`.

Let `Γ` be a finitely generated group with finite symmetric generating set `S`, let `G` be its right
Cayley graph (edges `{g,gs}`, `s∈S`), and let `ω` be a random spanning forest of `G` whose law is
invariant under left multiplication by `Γ`.

1. **(Cost formula.)** If `ω` has exactly `k<∞` components almost surely, then `Γ` admits a free
   p.m.p. treeable action, hence `Γ` is treeable, and
   `C_*(Γ) = 1 + (E deg_ω(e)/2 − 1)/k`.
2. **(Price-one obstruction.)** If `Γ` is nonamenable and `C_*(Γ)=1` (in particular, if `Γ` has fixed
   price 1), then `ω` has infinitely many components almost surely.
3. **(Open class.)** On every Cayley graph of every nonamenable group for which `p_c<p_u` is not already
   known from `fpbs-non-fixed-price-one-has-nonuniqueness`, and more generally whenever `C_*(Γ)=1`,
   the free and wired minimal and uniform spanning forests all have infinitely many components almost
   surely.

**Consequence for the goal.** Any route to `p_c<p_u` that passes through an invariant or factor-of-iid
spanning forest with finitely many components (for example a connected FMSF, or a forest with one
component per coset of a subgroup of finite index) cannot reach the open fixed-price-one class. The
invariant that kills it is `C_*(Γ)=1`, which means non-treeability for nonamenable `Γ`. The step where
every such route fails is the hair treeing of the coset lift in the proof route.

Sanity checks:

- On the 4-regular tree of `F_2` (`C_*=2`), `k=2` would need `E deg=6>4`, so no such forest exists.
  With `k=1`, the tree itself gives `E deg=4` and `C_*=2`.
- On `F_2×Z/2` with the Cayley graph `T_4□K_2` (`C_*=3/2`), take `k=1` with one sheet tree plus
  hairs. Then `E deg=3`, and the formula gives `3/2`.
- For amenable `Γ` the formula forces `E deg=2`, which is consistent with the known amenable case.
