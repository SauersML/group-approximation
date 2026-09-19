---
rg: 2
id: fpbs-no-infinite-cluster-bounded-in-height-proof
kind: route
title: A mass transport onto the top set forbids infinite clusters with finitely many highest points, and one finite-energy flip at a highest point turns any bounded-above infinite cluster into one
target: fpbs-no-infinite-cluster-bounded-in-height
requires: []
---

**Notation.** As in the target. `Gamma` acts on `G` by left multiplication,
`g . x = gx`. This is a graph automorphism, and it acts on configurations by
`(g omega)(e) = omega(g^(-1) e)`. The Bernoulli measure `P = P_p` is
invariant under this action. For a cluster `C` that is bounded above, let

```text
top(C) = max { h(x) : x in C },    Top(C) = { x in C : h(x) = top(C) }.
```

`Top(C)` is nonempty, because `h` takes integer values that are bounded above
on `C`, so the maximum is attained.

**Equivariance.** Since `h(gx) = h(g) + h(x)`, the cluster of `gx` in
`g omega` is `g K_x(omega)`, and it is bounded above iff `K_x(omega)` is.
In that case `Top(K_(gx)(g omega)) = g Top(K_x(omega))`.

**Mass transport principle.** Let `f(x,y;omega) >= 0` satisfy
`f(gx,gy;g omega) = f(x,y;omega)`. Then

```text
E sum_y f(o,y) = E sum_x f(x,o).
```

*Proof.* We have `E f(x,o) = E f(o, x^(-1))`, by invariance under
`g = x^(-1)`. Summing over `x` and substituting `y = x^(-1)` gives the
identity. This is where unimodularity enters: counting measure on `Gamma` is
invariant under inversion.

## Step 1: no infinite cluster has a finite top set

Let `B` be the event that some infinite cluster is bounded above and has
`Top` finite. Define

```text
f(x,y;omega) = 1{ K_x infinite, bounded above, |Top(K_x)| < infinity, y in Top(K_x) } / |Top(K_x)|.
```

By equivariance, `f` is diagonally invariant.

- **Out-mass.** `sum_y f(o,y) <= 1`, so `E sum_y f(o,y) <= 1`.
- **In-mass.** On the event `A_o = { o in Top(K_o), K_o infinite, |Top(K_o)| < infinity }`,
  every `x in K_o` has `K_x = K_o`. So
  `sum_x f(x,o) = |K_o| / |Top(K_o)| = infinity`.

The mass transport principle gives `infinity * P(A_o) <= 1`, so `P(A_o) = 0`.
By invariance, `P(A_x) = 0` for every `x`. Every cluster in `B` has a
vertex `x` of its top set, and then `A_x` holds. So `B ⊂ ∪_x A_x`, and
`P(B) = 0`.

## Step 2: a flip at a highest point

Let `A` be the event that some infinite cluster is bounded above. Suppose
`P(A) > 0`.

**A highest point at the origin.** Every cluster in `A` has a nonempty top
set, so `A ⊂ ∪_x { x in Top(K_x), K_x infinite and bounded above }`. By
countable additivity and invariance, the event

```text
A_* = { o in Top(K_o), K_o infinite and bounded above }
```

has `P(A_*) > 0`. On `A_*`, write `C = K_o` and note `top(C) = h(o) = 0`.

**The flip set.** Let `B_1 = {o} ∪ S` be the ball of radius `1`, and let
`E_1` be the finite set of edges with at least one endpoint in `B_1`. Since
`h` is nonzero and `S` generates `Gamma`, some `s in S` has `h(s) != 0`.
Since `S = S^(-1)`, we may fix `s_+ in S` with `h(s_+) >= 1`.

**The construction.** Fix `omega in A_*`.

1. **An infinite piece.** Delete the edges of `E_1` from `C`. Every
   component of what remains of `C \ B_1` contains a vertex `u` joined by an
   `omega`-open edge of `E_1` to a vertex of `B_1`. Otherwise that component
   could not be connected to `o in B_1` inside `C`. The set of vertices
   outside `B_1` adjacent to `B_1` is finite, so there are finitely many
   components. Their union `C \ B_1` is infinite, so one component `C_1` is
   infinite.

   Choose such a `C_1`, a vertex `u in C_1` and an `omega`-open edge
   `{u, v_0}` of `E_1` with `v_0 in B_1`, by a fixed deterministic rule.
   Every vertex of `C_1` has height `<= 0`, since `C_1 ⊂ C`.
2. **The new configuration.** Let `pi` be the path `v_0, o, o s_+`. If
   `v_0 = o`, it is `o, o s_+`; if `v_0 = o s_+`, it is the single vertex
   `v_0`. All its edges lie in `E_1`. Define `omega'` as follows:
   - `omega' = omega` off `E_1`;
   - on `E_1`, `omega'` opens exactly the edge `{u, v_0}` and the edges of
     `pi`, and closes every other edge.
3. **The new cluster.** Every edge incident to a vertex of `B_1` lies in
   `E_1`. So in `omega'` the only open edges at the vertices of `pi` are the
   edges of `pi` and `{u, v_0}`. Every `omega'`-open edge leaving `C_1`
   is `omega`-open and off `E_1`, so it stays inside `C_1` (because `C_1`
   is a component of `C` with the edges of `E_1` removed), or it is
   `{u, v_0}`. Hence

   ```text
   K_u(omega') = C_1 ∪ pi.
   ```

   This set is infinite. Its heights are at most `max(0, h(s_+)) = h(s_+)`.
   The value `h(s_+) >= 1` is attained only on `pi`, since `C_1` has heights
   `<= 0`, so its top set is a nonempty subset of `pi`. In the case
   `v_0 = o s_+`, the top set is `{o s_+}`, or a subset of `pi`
   again.

   So `omega'` lies in the event `B` of Step 1.

**Finite energy.** The pattern `xi = omega'|E_1` depends on `omega` only
through the rule of item 1, and takes one of finitely many values. So some
`xi` has `P(A_*^xi) > 0`, where `A_*^xi` is the part of `A_*` on which the
construction produces `xi`. Consider the map `Phi_xi : omega -> omega'`,
which resets `E_1` to `xi`. It changes only coordinates in `E_1`, and
`omega'` is determined by `(omega|_(E_1^c), xi)`. Hence

```text
P(Phi_xi(A_*^xi)) >= min(p, 1-p)^(|E_1|) P(A_*^xi) > 0.
```

This holds because `Phi_xi(A_*^xi)` contains the cylinder
`{ eta : eta|_(E_1) = xi, eta|_(E_1^c) in proj(A_*^xi) }`, and that
cylinder has probability `P(xi) P(proj(A_*^xi)) >= min(p,1-p)^(|E_1|) P(A_*^xi)`.
But `Phi_xi(A_*^xi) ⊂ B`, and `P(B) = 0` by Step 1. This is a
contradiction, so `P(A) = 0`.

## Step 3: bounded below

`-h` is also a nonzero homomorphism `Gamma -> Z`. Applying Steps 1–2 to `-h`
shows that a.s. no infinite cluster is bounded below. This proves item 1.

## Step 4: crossings and leaking half-space components

**Item 2.** Suppose that, with positive probability, some infinite cluster
has finitely many open edges between `L_n` and `U_n`. If this set of edges
is empty, the cluster lies in `L_n` or in `U_n`, which contradicts item 1.
Otherwise, by countable additivity, some fixed finite nonempty edge set `F`
has `P(A_F) > 0`, where `A_F` is the event that some infinite cluster `C` has
exactly `F` as its set of open crossing edges.

Close the edges of `F`. The resulting configuration has probability at least
`((1-p)/p)^(|F|) P(A_F)`, by the same cylinder argument. In it, `C` splits
into at most `|F| + 1` components, and each of them is a cluster of the new
configuration. The reason is that every open edge leaving a component was an
edge of `C`, and it is either in `F`, hence now closed, or inside the
component. One component is infinite, and it contains no crossing edge, so it
lies in `L_n` or in `U_n`. That contradicts item 1 for the new configuration,
an event of positive probability.

**Item 3.** Let `D` be an infinite component of the open subgraph induced on
`L_n`. Every `omega`-open edge leaving `D` goes into `U_n`, because `D` is a
component inside `L_n`. Suppose, with positive probability, some such `D`
has a finite set `F` of open edges into `U_n`, where `F` ranges over
countably many finite sets. Closing `F` makes `D` an infinite cluster
contained in `L_n`, with positive probability, which contradicts item 1. The
statement for `U_n` is symmetric.

## Step 5: the corollary

On `{|K_o| = infinity}`, item 1 says `K_o` is not bounded above, so it meets
`U_n` for every `n`. Hence `P(o <-> U_n) >= theta(p)`.

## Where the calibration fails

On the `3`-regular tree with the Busemann height of an end, the flip of
Step 2 is harmless. The mass transport of Step 1 is not available: height
differences are invariant only under `Aut_xi(T)`, which is nonunimodular.
The identity `E f(x,o) = E f(o,x^(-1))` has no analogue there, since there
is no group element inverting a pair and preserving the height. Every
supercritical cluster there has a single top vertex, which is consistent with
this.
