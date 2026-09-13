---
rg: 2
id: sl2-laurent-integers-splits-over-gamma0-t-proof
kind: route
title: "SL_2(Z[t,t^-1]) is edge-transitive on the t-adic Bruhat-Tits tree, hence an amalgam"
target: sl2-laurent-integers-splits-over-gamma0-t
requires: []
---

Notation: `R = Z[t,t^{-1}]`, `G = SL_2(R)`, `K = SL_2(Q[[t]])`, `D = diag(1,t)`.

**Tree.** Let `T` be the Bruhat–Tits tree of `SL_2(Q((t)))`: vertices are homothety
classes of `Q[[t]]`-lattices in `Q((t))^2`, and two classes are adjacent when they
have representatives `L ⊋ L' ⊋ tL`. `G ⊂ SL_2(Q((t)))` acts on `T`. Elements of
`SL_2` preserve the type of a vertex (the parity of `v_t(det)` of a lattice basis),
so the action has no inversions and vertices of different type lie in different
orbits.

**Step 1: two stabilizers.** Let `v_0 = [L_0]` with `L_0 = Q[[t]]^2`, and
`v_1 = [D L_0] = [Q[[t]]e_1 ⊕ tQ[[t]]e_2]`, a neighbour of `v_0`.
If `g ∈ SL_2(Q((t)))` and `gL_0 = λL_0`, comparing determinants gives
`v_t(λ) = 0`, so `gL_0 = L_0`; hence `Stab(v_0) = K`. Therefore
`Stab_G(v_0) = SL_2(R ∩ Q[[t]]) = SL_2(Z[t]) = A`.
Since `D ∈ GL_2(R)`, conjugation by `D` preserves `GL_2(R)`, and
`Stab_G(v_1) = G ∩ DKD^{-1} = D A D^{-1}`. Explicitly
`D^{-1}[[a,b],[c,d]]D = [[a, tb],[t^{-1}c, d]]`, so
`D A D^{-1} = { a, d ∈ Z[t], b ∈ t^{-1}Z[t], c ∈ tZ[t] }`, and
`A ∩ DAD^{-1} = { a, b, d ∈ Z[t], c ∈ tZ[t] } = Gamma_0(t)`.

**Step 2: stabilizers are transitive on neighbours.** The neighbours of `v_0` are the
lattices strictly between `L_0` and `tL_0`, i.e. the lines in `L_0/tL_0 = Q^2`,
i.e. `P^1(Q)`. The group `K` acts on them through reduction `t ↦ 0`,
`K → SL_2(Q)`. The reduction of `A = SL_2(Z[t])` is `SL_2(Z)` (surjective, since
`SL_2(Z) ⊂ A`), and `SL_2(Z)` acts transitively on `P^1(Q)`: a point `[m:n]` with
`gcd(m,n) = 1` is the image of `[1:0]` under a matrix of `SL_2(Z)` with first
column `(m,n)`. So `Stab_G(v_0)` is transitive on the neighbours of `v_0`.
Conjugating by `D`, the neighbours of `v_1` are the lines of `DL_0/tDL_0 ≅ Q^2`,
and `Stab_G(v_1) = DAD^{-1}` acts on them through `D SL_2(Z) D^{-1}`, again
transitively.

**Step 3: one orbit of edges.** Claim: every vertex lies in `Gv_0 ∪ Gv_1`, and every
edge lies in `G·[v_0,v_1]`. Induct on the distance from `v_0`. Let `y` be adjacent to
a vertex `x` already known to lie in `Gv_0 ∪ Gv_1`. If `x = gv_0`, then
`Stab_G(x) = g Stab_G(v_0) g^{-1}` is transitive on the neighbours of `x`, one of
which is `gv_1`; so `y = hgv_1` and `[x,y] = hg[v_0,v_1]` for some `h ∈ Stab_G(x)`.
If `x = gv_1` the same argument uses Step 2 for `v_1`. Since `T` is connected, the
claim follows. So the edge `[v_0,v_1]` is a fundamental domain for `G` on `T`.

**Step 4: Bass–Serre.** A group acting without inversion on a tree with an edge as
fundamental domain is the amalgam of the two vertex stabilizers over the edge
stabilizer (Serre, *Trees*, §I.4). Hence
`G = A *_{Gamma_0(t)} DAD^{-1}`.

**Other end.** Replace `t` by `t^{-1}` (an automorphism of `R`) to get the
decomposition over `Gamma_0(t^{-1}) ⊂ SL_2(Z[t^{-1}])` from the tree of
`Q((t^{-1}))`.

**Model test.** Over a field `k` in place of `Z`, Step 2 holds because `SL_2(k)` is
transitive on `P^1(k)`, giving the known `SL_2(k[t,t^{-1}]) = SL_2(k[t]) *_{Gamma_0(t)} D SL_2(k[t]) D^{-1}`.
The argument needs only that `SL_2` of the constant ring acts transitively on
`P^1` of its fraction field. That holds for `Z` (a PID) and fails for a ring of
integers with nontrivial class group, where the quotient graph has more edges.
