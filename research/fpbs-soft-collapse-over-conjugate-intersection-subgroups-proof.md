---
rg: 2
id: fpbs-soft-collapse-over-conjugate-intersection-subgroups-proof
kind: route
title: Select left cosets of H iid, and join their sheets by random-walk excursions launched from the infinite itinerary-stable subgroup H ∩ v_1 H v_1^-1 ∩ ... ∩ v_d H v_d^-1
target: fpbs-soft-collapse-over-conjugate-intersection-subgroups
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
---

Notation as in the target. `Gamma` acts on itself, on `Gamma/H` (left cosets)
and on subgraphs of `G = Cay(Gamma,S)` by left multiplication. Edges of `G` are
`{x, xs}` for `s in S`. "Invariant" means `Gamma`-invariant in law. Theorem A of
`fpbs-soft-collapse-iff-invariant-sparse-spines` is used verbatim: *for
`Gamma` infinite, nonamenable and finitely generated, `G` carries a soft
collapse family if and only if it has invariant sparse spines*. Invariant
sparse spines there means: for every `eps > 0` a random subgraph `L` with
invariant law that is a.s. connected and infinite and has
`P(o in V(L)) <= eps`. No ergodicity of `L` is required. The last clause of
Theorem 1 follows from Theorem A, and Corollary 4 then follows by the argument
of Corollary C there. The work is Theorem 1, Proposition 2 and Corollary 3.

For a word `v = s_1 ... s_d` in `S` write `v_j = s_1 ... s_j` for the prefix
elements (`v_0 = e`), and `x·v` for the path `x v_0, x v_1, ..., x v_d` in `G`.

## 1. Construction

Fix `H` satisfying (C), generators `h_1, ..., h_k` of `H`, and words `w_j` in
`S` with `w_j = h_j` in `Gamma`. Let `U ⊆ Gamma` be the set of prefix elements
of all `w_j`, so `e in U` and `|U| <= 1 + sum_j |w_j|`. Fix `eps, eta in (0,1]`.

Independent random inputs:

* `xi = (xi_c)_{c in Gamma/H}`, iid Bernoulli(`eps`). Let
  `A = {c : xi_c = 1}`.
* For every `x in Gamma`, a sequence `(sigma^x_n)_{n >= 1}` iid uniform on
  `S`, and `lambda_x` uniform on `[0,1]`. All of these are independent of each
  other and of `xi`. Put `X^x_n = x sigma^x_1 ... sigma^x_n` (`X^x_0 = x`), a
  simple random walk on `G` started at `x`.

Left multiplication by `gamma` acts on the inputs by
`(gamma xi)_c = xi_{gamma^{-1} c}` and
`(gamma sigma)^x = sigma^{gamma^{-1} x}`,
`(gamma lambda)_x = lambda_{gamma^{-1} x}`. This preserves the joint law,
because each family is iid over a set that `gamma` permutes.

**Sheets.** For a coset `c`, let `Sh_c` be the union of the paths `x·w_j` over
`x in c` and `j = 1, ..., k`. Then `gamma Sh_c = Sh_{gamma c}`.

**Lemma 1.1.** `Sh_c` is connected and infinite, and contains every vertex of
`c`.

*Proof.* Each path `x·w_j` starts at `x in c` and ends at `x h_j in c`, so
every vertex of `Sh_c` is joined inside `Sh_c` to a vertex of `c`. Two vertices
`x, x h` of `c` are joined, since `h` is a product of the `h_j^{±1}`, and the
step from `y` to `y h_j^{-1}` uses the path `(y h_j^{-1})·w_j`, which ends at `y`.
`c` is infinite because `H` is. ∎

**Connectors.** For `x` with `xH in A`, let
`T_x = inf{n >= 1 : X^x_n H in A and X^x_n H ≠ xH}`, with `inf ∅ = ∞`. The
connector `C_x` is the path `X^x_0, ..., X^x_{T_x}` if `xH in A`, `T_x < ∞` and
`lambda_x < eta/(T_x + 1)`. Otherwise `C_x` is empty.

**The spine.** `L` is the union of `Sh_c` over `c in A` and of `C_x` over
`x in Gamma`. `L` is a measurable function of the inputs, and
`gamma L(inputs) = L(gamma inputs)`, because the definitions of `A`, `Sh_c`,
`T_x` and `C_x` commute with left multiplication. So `L` has invariant law.

Each nonempty connector `C_x` starts at `x in xH ⊆ Sh_{xH}` and ends at
`X^x_{T_x} in X^x_{T_x} H ⊆ Sh_{X^x_{T_x} H}`, with both cosets in `A`
(Lemma 1.1). So every component of `L` contains a sheet.

## 2. Density

**Lemma 2.1.** `P(o in V(Sh_c) for some c in A) <= |U| eps`.

*Proof.* The vertices of `Sh_c` are the elements `x u` with `x in c` and
`u in U`. If `o = e = x u`, then `x = u^{-1}` and `c = u^{-1} H`. So at most
`|U|` cosets have `o` in their sheet, and each lies in `A` with probability
`eps`. ∎

**Lemma 2.2.** `P(o in V(C_x) for some x) <= eta eps`.

*Proof.* By the union bound it suffices to bound `sum_x P(o in V(C_x))`.
Left multiplication by `x^{-1}` maps `C_x` to `C_e` for the transformed
inputs and `o` to `x^{-1}`. The law is invariant, so
`P(o in V(C_x)) = P(x^{-1} in V(C_e))`. Summing over `x` gives
`E|V(C_e)|`. The vertex count of `C_e` is at most `T_e + 1` when `C_e` is
nonempty. Since `lambda_e` is independent of `(xi, X^e)`,

`E|V(C_e)| <= E[ 1{xi_H = 1} 1{T_e < ∞} (T_e + 1) min(1, eta/(T_e + 1)) ]
<= eta P(xi_H = 1) = eta eps`. ∎

So `P(o in V(L)) <= (|U| + eta) eps`, which is as small as desired.

**Lemma 2.3.** `L` is a.s. nonempty and infinite.

*Proof.* `[Gamma:H] = ∞`, so `Gamma/H` is infinite. The `xi_c` are iid
Bernoulli(`eps`) with `eps > 0`, so `A` is a.s. infinite, in particular
nonempty. `L` then contains an infinite sheet (Lemma 1.1). ∎

## 3. Connectivity

By Lemma 1.1 and the last paragraph of section 1, `L` is connected as soon as
`Sh_q` and `Sh_{q'}` lie in one component of `L` for all `q, q' in A`. Condition
on `xi`, i.e. fix `A` (with `A` infinite). The walks and the `lambda_x` stay iid
and independent of `A`. There are countably many pairs `(q, q')`, so it suffices
to show that, for fixed `A` and fixed `q ≠ q'` in `A`, the sheets `Sh_q` and
`Sh_{q'}` are joined in `L` with conditional probability one.

**Chain of selected cosets.** Pick `y in q` and a word `s_1 ... s_n` with
`y s_1 ... s_n in q'`. Put `y_j = y s_1 ... s_j` and `r_j = y_j H`, so
`r_0 = q` and `r_n = q'`. Define `i_0 = 0` and, while `r_{i_m} ≠ q'`,

`i_{m+1} = min{ j > i_m : r_j in A and r_j ≠ r_{i_m} }`.

The set is nonempty, since `j = n` belongs to it. The indices increase strictly,
so the procedure stops at some `i_M` with `r_{i_M} = q'`. Every `r_{i_m}` is in
`A`. By Lemma 1.1 it suffices to join `Sh_{r_i}` to `Sh_{r_{i'}}` for each
consecutive pair `i = i_m`, `i' = i_{m+1}`.

**One segment.** Let `z = y_i`, `d = i' - i >= 1`, and let `v` be the word
`s_{i+1} ... s_{i'}`, with prefix elements `v_0 = e, v_1, ..., v_d`. So
`z v_j = y_{i+j}` and `z v_j H = r_{i+j}`. By minimality of `i'`, for
`0 < j < d` either `r_{i+j} ∉ A` or `r_{i+j} = r_i`, and
`r_{i'} in A`, `r_{i'} ≠ r_i`.

Let `H_v = H ∩ v_1 H v_1^{-1} ∩ ... ∩ v_d H v_d^{-1}`. By (C), applied to
`F = {e, v_1, ..., v_d}`, `H_v` is infinite.

**Lemma 3.1 (itinerary stability).** For `h in H_v` and `x = z h`,
`x v_j H = z v_j H = r_{i+j}` for `j = 0, ..., d`.

*Proof.* `h in v_j H v_j^{-1}` gives `v_j^{-1} h v_j in H`, so
`z h v_j H = z v_j (v_j^{-1} h v_j) H = z v_j H`. ∎

For `h in H_v` and `x = z h`, let `E_x` be the event that
`sigma^x_j = s_{i+j}` for `j = 1, ..., d` and `lambda_x < eta/(d + 1)`.

**Lemma 3.2.** On `E_x`, `C_x` is the path `x·v`. It joins `Sh_{r_i}` to
`Sh_{r_{i'}}`.

*Proof.* On `E_x`, `X^x_j = x v_j`, so `X^x_j H = r_{i+j}` by Lemma 3.1.
`xH = r_i in A`. For `0 < j < d` the coset `r_{i+j}` is not in `A` or equals
`xH`, so `T_x > j`. At `j = d`, `r_{i'} in A` and `r_{i'} ≠ xH`, so `T_x = d`.
Since `lambda_x < eta/(d+1) = eta/(T_x + 1)`, `C_x = x·v`. It starts at
`x in r_i ⊆ Sh_{r_i}` and ends at `x v_d in r_{i'} ⊆ Sh_{r_{i'}}`. ∎

**Lemma 3.3.** Conditionally on `A`, a.s. some `E_x` with `x in z H_v` occurs.

*Proof.* The event `E_x` depends only on `sigma^x` and `lambda_x`, so the
`E_x` for distinct `x` are independent, each with probability
`|S|^{-d} eta/(d+1) > 0` (here `S` is a set, so each prescribed step has
probability `1/|S|`). `z H_v` is infinite. The probability that no `E_x`
occurs is `prod (1 - |S|^{-d} eta/(d+1)) = 0`. ∎

By Lemmas 3.2 and 3.3, consecutive chain sheets are joined a.s., so `Sh_q` and
`Sh_{q'}` are joined a.s. The chain depends only on `(q, q', A)` and the fixed
word, so there are countably many events of conditional probability one.
Integrating over `A` shows that `L` is a.s. connected. With sections 1 and 2,
this proves Theorem 1. ∎

**Where (C) is used, and where it cannot be weakened here.** It is used only in
Lemma 3.3, to get infinitely many independent trials. Launching from a single
point `z` would give one trial of probability less than one, and the trials
from `z h` with `h ∉ H_v` follow different coset itineraries, whose selected
status is uncontrolled. In `F_2` with `H = <a>`, `H_v` is finite for `v = b`
(`<a> ∩ b <a> b^{-1} = {e}`), which is the failure noted in
`fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups`.

## 4. Proposition 2

Let `H` be infinite, finitely generated and of infinite index, and `F ⊆ Gamma`
finite.

(a) Each `g H g^{-1} ∩ H` has finite index in `H`. A finite intersection of
finite-index subgroups of `H` has finite index in `H`, so
`∩_{g in F} g H g^{-1} ⊇ ∩_{g in F} (g H g^{-1} ∩ H)` is infinite.

(b) If `N ⊴ Gamma` is infinite and `N <= H`, then `g H g^{-1} ⊇ g N g^{-1} = N`
for every `g`, so the intersection contains `N`.

(c) Let `Gamma` act by automorphisms on a connected locally finite graph `X`,
`H = Stab(v)`, with `Gamma v` infinite. Then `[Gamma:H] = |Gamma v| = ∞`. For
`g in Gamma` let `R = d(v, gv)`. The ball `B(v,R)` is finite and `H` permutes
it, so the pointwise stabiliser `K_R` of `B(v,R)` in `H` has finite index in
`H`. `K_R` fixes `gv`, so `K_R <= Stab(gv) = g H g^{-1}`. Hence `H` is
commensurated and (a) applies. ∎

## 5. Corollary 3

**`BS(m,n)`, `|m|, |n| >= 2`.** `H = <a>` is infinite cyclic (the base group
of an HNN extension embeds). The map `a -> 0`, `t -> 1` onto `Z` kills `H`, so
`[Gamma:H] = ∞`. From `t a^m t^{-1} = a^n`, `t H t^{-1} ∩ H ⊇ <a^n>`, which has
index `|n|` in `H`, and `t<a^m>t^{-1} = <a^n>` has index `|m|` in `t H t^{-1}`.
The commensurator `{g : g H g^{-1}` commensurable with `H}` is a subgroup and
contains `a` and `t`, so it is `Gamma`. (C) follows by Proposition 2(a). These
groups are nonamenable exactly when `|m|, |n| >= 2` (standard: the Bass--Serre
tree is then a regular tree of degree `|m| + |n| >= 4` with an action that is
not elementary, and `BS(m,n)` contains a nonabelian free subgroup).

**`SL_2(Z[1/p])`.** It acts on the Bruhat--Tits tree `T_{p+1}` of
`SL_2(Q_p)`, which is locally finite. The stabiliser of the vertex given by the
lattice `Z_p^2` is `SL_2(Z[1/p]) ∩ SL_2(Z_p) = SL_2(Z)`, since
`Z[1/p] ∩ Z_p = Z`. `diag(p, 1/p)` acts as a translation of length 2, so the
orbit is infinite. `SL_2(Z)` is infinite and finitely generated, so (C) holds by
Proposition 2(c). `SL_2(Z[1/p])` is finitely generated (by the upper and lower
unipotents `u`, `u^T` and `diag(p, 1/p)`), and nonamenable because it contains
`SL_2(Z)`.

**Graphs of groups.** Let `Gamma = pi_1` of a finite graph of groups with
finitely generated infinite vertex groups and all edge groups of finite index in
the adjacent vertex groups, and let `X` be the Bass--Serre tree. The degree of a
vertex over `v` is `sum_e [G_v : G_e]` over edges `e` at `v`, which is finite,
so `X` is locally finite. Vertex stabilisers are conjugates of vertex groups.
If `X` is infinite, every vertex orbit is infinite. Otherwise some stabiliser
`Stab(w)` would have finite index. Adjacent stabilisers are commensurable by
(c), so by connectedness all stabilisers would have finite index, and the
finitely many orbits would be finite, a contradiction. (C) holds for a vertex
group by Proposition 2(c).

**Normal subgroups.** If `N` is an infinite, finitely generated normal
subgroup of infinite index, take `H = N` in Proposition 2(b). More generally,
take any finitely generated infinite-index `H` containing an infinite normal
subgroup.

## 6. Corollary 4

For nonamenable `Gamma`, Theorem 1 and Theorem A give a soft collapse family on
every Cayley graph. It satisfies every admissible input (a)--(b), and for every
`t > p_c` it has a unique infinite cluster. An argument using only those inputs
to prove nonuniqueness at some `t > p_c` would therefore also apply to this
family, a contradiction. The argument is that of Corollary C of
`fpbs-soft-collapse-iff-invariant-sparse-spines`. ∎

## 7. Remark on cost (not load-bearing)

Let `omega` be the input configuration of section 1 and `beta` iid uniform
labels on `Gamma`, independent of `omega`. The action on `(omega, beta)` is
free and p.m.p. Define a graphing with two kinds of edges: the edges of `L`, and
for each vertex `x ∉ V(L)` one edge to the neighbour `xs` with
`d(xs, L) = d(x, L) - 1` of smallest label. Distances are finite because `L` is
nonempty. The second kind never forms 2-cycles, so the edges are distinct, and
every vertex is joined to the connected graph `L`. So the graphing generates the
orbit relation, and its cost is at most
`(|S|/2) P(o in V(L)) + P(o ∉ V(L)) <= 1 + |S| (|U| + eta) eps / 2`. Letting
`eps -> 0` gives infimal cost one.
