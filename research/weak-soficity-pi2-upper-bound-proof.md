---
rg: 2
id: weak-soficity-pi2-upper-bound-proof
kind: route
title: Glebsky's product-quotient characterization plus the finiteness of normal-closure expressions in a direct product
target: weak-soficity-recognition-has-a-pi2-upper-bound
requires:
  - glebsky-weak-soficity-is-metric-free
---

Glebsky's Lemma 1.2 (recorded in
[[glebsky-weak-soficity-is-metric-free]]) says `K` is weakly sofic iff
`K` embeds in `D / M` for some direct product `D` of finite groups
(indexed by an arbitrary set) and some normal subgroup `M`.

**Bounded-area normal closures.**  In any group `D`, the normal closure
of a set `S` consists of finite products of conjugates of elements of
`S u S^-1`.  For `D = prod_i H_i` and `S` the set of relator tuples
`(r(h_i))_i`, `r in R`, a tuple `(w(h_i))_i` lies in the normal closure
iff there is a single template `T = (r_1^{e_1}, ..., r_m^{e_m})` and
tuples `c_1, ..., c_m in D` with `w(h_i) = prod_j c_{j,i} r_j(h_i)^{e_j}
c_{j,i}^{-1}` for every `i` simultaneously.

**(=>)**  Let `K = <X | R>` embed in `D/M` via `x |-> (h_i(x))_i`.  Given
`W` all of whose words are nontrivial in `K`, and a template `T`, for each
`w in W` the tuple `(w(h_i))` is not in `M`, hence not in the normal
closure of the relator tuples, so for some coordinate `i(w)` and all
`c in H_{i(w)}^m` the identity `w(h_{i(w)}) = prod_j c_j r_j(h_{i(w)})^{e_j}
c_j^{-1}` fails.  Put `H = prod_{w in W} H_{i(w)}` with the product
assignment; a product-of-conjugates identity in `H` would project to one
in each factor, so `H, h` is a certificate.

**(<=)**  Suppose every challenge `(W, T)` with `W` nontrivial has a
certificate `(H_{W,T}, h_{W,T})`.  Let `D = prod_{(W,T)} H_{W,T}` with
the product assignment `h`, and `M` the normal closure in `D` of the
relator tuples.  The map `x |-> (h(x))` sends every relator into `M`, so
it induces `K -> D/M`.  If `w` is nontrivial in `K` and `(w(h_{W,T}))`
were in `M`, there would be a template `T_0` and conjugating tuples
working in every coordinate, in particular in the coordinate
`(W, T) = ({w}, T_0)`, contradicting the certificate.  So `K` embeds in
`D/M` and is weakly sofic.

**Arithmetic.**  The first disjunct of (WS1) is the r.e. word problem.
The second is a search over finite groups (multiplication tables) and
assignments whose body is a finite check.  Templates and word lists are
enumerated with the presentation's relators.  So (WS1) is `Pi^0_2`.
Weak soficity passes to subgroups, contains the residually finite groups
(they embed in products of finite groups with `M = 1`), and is local
(finitely generated subgroups of `D/M` suffice, or clause 2 of
[[local-approximation-properties-are-marked-closed]] applied to the
Glebsky--Rivera metric definition), so the second-level Rice theorem
applies as soon as some group fails weak soficity.
