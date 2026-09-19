# Cycle tails are not invariants of the group-ring chain complex

Worker swarm-0917-w13-w13-fp-pull, group-rings transplant on
`fpbs-bernoulli-cycle-tail-compactness`. Conventions are those of
`research/artifacts/fpbs/docs/cost-cycle-structure.md`, Sections 1, 3 and 4:
simple graphings (no loops, no duplicate unordered edges), `C_1(Phi)` the
Hilbert R-module of square-summable antisymmetric edge chains, `Z(Phi)` the
closed span of the finite simple cycles, `Z_L(Phi)` the closed span of simple
cycles of length at most `L`, `z = dim_R Z`, `z_L = dim_R Z_L`,
`tau_L = z - z_L`.

## 0. Dictionary

Let `Gamma` be infinite and finitely generated, `X = 2^Gamma` with the product
measure, `R` the orbit relation of the Bernoulli shift `b`. Let `A` be the
ring of finite sums `sum_g f_g u_g` with `f_g` locally constant `Z`-valued on
`X`. The Q-span of cylinder indicators equals the Q-span of the characters of
`(Z/2)^(Gamma)`, so `A tensor Q = Q[Z/2 wr Gamma]` inside
`L(R) = L(Z/2 wr Gamma)`. A cylinder graphing `Phi` has finitely many pieces
`g_i` restricted to clopen sets `D_i`. Its boundary `partial_1` is a matrix
over `A`, and so is every operator below. Call an operator on edge chains
*of propagation at most M* if it moves each edge to chains on edges joined
to it by Phi-paths of length at most `M`.

Write `F_r` for the finite set of labels (group elements) of Phi-words of
length at most `r`, and `d(x, y)` for the Phi-graph distance.

## 1. Statement

**Theorem.** Let `Phi` be a cylinder graphing generating `R`, and let
`L >= 3`. There are a clopen set `U` of positive measure and
`gamma_s, gamma_l in Gamma` such that `Phi_s = Phi cup gamma_s|U` and
`Phi_l = Phi cup gamma_l|U` are simple cylinder graphings generating `R`,
and:

1. `c(Phi_s) = c(Phi_l) = c(Phi) + mu(U)`;
2. there is a bounded invertible map `W : C_1(Phi_s) -> C_1(Phi_l)` with
   `partial_1^l W = partial_1^s`, `W` and `W^{-1}` unipotent with entries in
   `A` and finite propagation, and `W Z(Phi_s) = Z(Phi_l)`;
3. `tau_L(Phi_l) >= tau_L(Phi_s) + mu(U)`, and in fact
   `tau_L(Phi_l) = tau_L(Phi) + mu(U)` and `tau_L(Phi_s) <= tau_L(Phi)`.

So the augmented complexes `C_1 -> C_0 -> Z` of `Phi_s` and `Phi_l`,
together with their finite-cycle submodules, are isomorphic over `A`
by an isomorphism that is the identity on `C_0`. The two graphings have
the same cost and the same `z`, while `tau_L` differs by at least `mu(U)`.

## 2. Choosing the chords and the set U

Work on the conull invariant set where the action is free. The pieces are
reversible, so every `F_r` is finite and symmetric.

*Clopen distance sets.* For fixed `h` and `r`, the set `{x : d(x, hx) <= r}`
is the finite union, over Phi-words of length at most `r` with label `h`,
of the sets where the word is a valid path from `x`. Each of these is a
finite intersection of piece domains and their translates, so it is clopen.

*Short chord.* The components are infinite and locally finite, so almost
every `x` has a vertex at distance exactly 2. Such a vertex is `hx` with
`h in F_2`. Since `F_2` is finite, some `gamma_s := h` has
`D := {x : d(x, gamma_s x) = 2}` of positive measure. `D` is clopen, and on
`D` the pair `{x, gamma_s x}` is not an edge of Phi.

*Long chord.* Pick `gamma_l` outside `F_L`. By freeness,
`d(x, gamma_l x) > L` for every `x`.

*Forbidden shifts.* Let `H = F_L \ {1}` and

    K_0 = {gamma_s^{+-1}, gamma_l^{+-1}} cup H cup H gamma_l
          cup gamma_l^{-1} H cup gamma_l^{-1} H gamma_l.

`K_0` is finite and does not contain 1. Indeed `h gamma_l = 1` or
`gamma_l^{-1} h = 1` would put `gamma_l` in `F_L`, and conjugating `h`
does not give 1.

*Pattern cylinder.* Fix a cylinder `[alpha]_{S_0}` contained in `D`. Take
`n` with `|K_0| 2^{-n/2} < 1`. Choose `E` of size `n` avoiding the finite
set `union_{k in K_0 cup {1}} k^{-1} S_0`. Put
`B = E cup union_{k in K_0} kE`, so `B` misses `S_0`. With
`(gx)(t) = x(g^{-1} t)`, we have `C_omega cap k C_omega` nonempty iff
`omega(s) = omega(k^{-1} s)` for all `s` in `B cap kB`. That set contains
`kE`, which gives the `n` constraints `omega(ke) = omega(e)`, `e in E`.

These constraints are edges of the orbit graph of `<k>`, whose components
are paths or cycles of length at least 2. So the constraints have rank at
least `n/2`. A uniformly random `omega in {0,1}^B` violates the condition
for a given `k` with probability at most `2^{-n/2}`. A union bound gives an
`omega` with `C_omega cap k C_omega` empty for every `k in K_0`.

Put `U_0 = C_omega cap [alpha]_{S_0}`. It is a nonempty cylinder, since
`B` misses `S_0`, and it lies in `D`. The clopen sets
`G_M = {x : d(x, gamma_l x) <= M}` increase to a conull set. Fix `M` with
`mu(U_0 cap G_M) > 0` and set `U = U_0 cap G_M`.

**(a)** `U cap kU` is empty for every `k in K_0`. In particular `U` is
disjoint from both `gamma_s U` and `gamma_l U`.

**(b)** Put `V = U cup gamma_l U`. For every `p in V`, the Phi-ball
`B(p, L)` meets `V` only in `p`. Suppose `q in V`, `q != p` and
`d(p, q) <= L`. Then `q = hp` with `h in H`, and the four cases give

- `q in U cap hU`,
- `U cap gamma_l^{-1} h U` nonempty,
- `U cap h gamma_l U` nonempty,
- `U cap gamma_l^{-1} h gamma_l U` nonempty.

Each contradicts (a).

*Simplicity.* A new edge `{x, gamma x}` with `x in U` is not an old edge:
`d = 2` for the short chord and `d > L >= 3` for the long one. Two new
edges `{x, gamma x} = {y, gamma y}` with `x != y` would force `y = gamma x`
and `x = gamma y`, so `y in U cap gamma U`, which is empty. So the new edge
set `N` has measure `mu(U)`, which proves item 1 of the Theorem. The
graphings still generate `R`, since the new edges lie in `R`, and each new
piece `gamma|U` has clopen domain.

## 3. The unipotent isomorphism W

Orient each new edge `e_x` from `x` to `gamma x`. Enumerate the Phi-words
with label `gamma_s` of length at most 2, and those with label `gamma_l` of
length at most `M`. For `x in U`, let `P_s(x)` and `P_l(x)` be the first
valid word in each list, read as a path of old edges. Such words exist
because `U` lies in `D` and in `G_M`. The set where a given word is the
first valid one is clopen. So the path-chain maps

    sigma_s, sigma_l : N -> C_1(Phi),   e_x |-> [P(x)],

are finite sums of cylinder partial isometries with integer coefficients.
They are entries of `A`, with propagation at most `M`. They are bounded,
since an old edge lies on `P(x)` for at most `|F_M|` points `x`. They
satisfy `partial [P(x)] = delta_{gamma x} - delta_x = partial e_x`.

Identify `C_1(Phi_s)` and `C_1(Phi_l)` with `C_1(Phi) + N`, using the same
`N`, indexed by `x in U`. Set

    E_s = [[1, -sigma_s], [0, 1]],   E_l = [[1, -sigma_l], [0, 1]].

Then `partial^s E_s = partial^l E_l = (partial, 0)`. Put
`W = E_l E_s^{-1} = [[1, sigma_s - sigma_l], [0, 1]]`. Then
`partial^l W = partial^s`, and `W^{-1} = [[1, sigma_l - sigma_s], [0, 1]]`.
Both are unipotent and R-equivariant, with entries in `A`.

*Finite cycles.* `Z(Phi)` is the closed R-span of measurable fields of
finitely supported cycles, because every finitely supported cycle of a
graph is an integer combination of simple cycles. `W` and `W^{-1}` take
finitely supported chains to finitely supported chains, and they
intertwine the boundaries. So `W Z(Phi_s)` lies in `Z(Phi_l)` and
`W^{-1} Z(Phi_l)` lies in `Z(Phi_s)`. Hence `W Z(Phi_s) = Z(Phi_l)`, which
proves item 2.

The same argument applied to `E_l`, which sends `e_x` to the finite cycle
`e_x - [P_l(x)]`, gives `E_l (Z(Phi) + N) = Z(Phi_l)`. Similarly for
`E_s`. Hence

    z(Phi_s) = z(Phi_l) = z(Phi) + mu(U),

without appeal to identity (3.1).

## 4. The tails

**Long chord.** Take a simple Phi_l-cycle of length at most `L` that uses
a new edge. By (a), distinct new edges share no vertex. So the cycle
contains an old segment of length between 1 and `L - 1` joining two
distinct points of `V`. With one new edge `e_x`, these points are
`gamma_l x` and `x`. With two or more, they are endpoints of different new
edges, which are distinct by simplicity. This contradicts (b). So the
simple cycles of length at most `L` are the same for `Phi_l` and `Phi`, and
`z_L(Phi_l) = z_L(Phi)` (the inclusion of `C_1(Phi)` is isometric and
equivariant). Hence `tau_L(Phi_l) = tau_L(Phi) + mu(U)`.

**Short chord.** Each `t_x = e_x - [P_s(x)]` is a simple 3-cycle, so it
lies in `Z_L(Phi_s)`. Let `pi_N` be the orthogonal projection onto `N`.
Then `pi_N t_x = e_x`, so the closure of `pi_N Z_L(Phi_s)` is all of `N`,
of dimension `mu(U)`. The kernel of `pi_N` on `Z_L(Phi_s)` contains
`Z_L(Phi)`. Additivity of dimension gives
`z_L(Phi_s) >= z_L(Phi) + mu(U)`, hence `tau_L(Phi_s) <= tau_L(Phi)`.

Subtracting the two tails gives item 3. QED.

## 5. What this kills, and what it does not

Call a quantity `J(Phi)` *length-blind* if it depends only on the
isomorphism class of the triple `(C_1 -> C_0 -> Z, Z(Phi))`. The
isomorphisms allowed are those given by unipotent matrices over `A` that
fix `C_0`, or any larger class of isomorphisms. Examples:

- `c`, `z` and `beta_1^(2)`;
- `Tor^A_*` and homology with any coefficient ring;
- the ranks of `partial_1` for every Sylvester matrix rank function on
  `A`, including vN ranks, ranks from finite quotients, and mod-p ranks
  (`W` has integer entries, so it reduces mod p);
- Lück-type approximants of these ranks;
- Fuglede--Kadison determinants, which are 1 on unipotent triangular
  matrices;
- K-theory classes.

The Theorem gives two graphings with equal length-blind data and equal
cost whose `tau_L` differ by at least `mu(U)`. So `tau_L` is not
length-blind. More sharply, `W` is not propagation-L: it replaces the short
path `P_s` by the long path `P_l`. `tau_L` is an invariant of the
**propagation filtration** of `A`, and group-ring tools that forget the
filtration cannot see it.

*Where the group-ring transplant dies.* The natural transplant of
`RG = beta_1` arguments, such as rank functions or approximation over the
ring `Q[Z/2 wr Gamma]`, controls only length-blind data. On this node that
data is already fixed: `z = c - 1 - beta_1^(2)` by (3.1). The step "rank
data bounds the tail" is exactly the step the Theorem blocks. Near the
minimum, length-blind data cannot separate `tau_L` from `z_L`. So a
length-blind argument proves the target only by proving `z(Phi_n) -> 0`
outright, which is `g = 0`. It gets no leverage from the tail
formulation.

*Honest scope.* The swap costs `mu(U)`. For eps-near-minimizers, the mass
of short chords that can be split off is at most `z_L <= L eps`, by (4.1).
So the Theorem does **not** rule out length-blind upper bounds
`tau_L <= F(J, c)` that tend to 0 near the minimum. It rules out only the
following:

- any identity expressing `tau_L` through length-blind data;
- any bound whose error beats the split-off short-chord mass.

It is not a refutation of `fpbs-bernoulli-cycle-tail-compactness`, and it
does not re-prove the gap equivalence of
`fpbs-cycle-tail-gap-near-minimum-iff-cost-betti-gap`. That gap
equivalence concerns lower gaps for `tau_L`, and this Theorem concerns
invariance.

*Survivors.* The surviving tools are the propagation-sensitive ones:

- the reduced circulation mass `T_L` of
  `fpbs-reduced-circulation-tail-bounds-cost-excess`, which weights routes
  by where they close up;
- the L-filled Laplacian of the Hodge dictionary, which uses exactly
  propagation-L cells;
- Morse matchings, which are combinatorial.

In group-ring language, the target asks for near-minimizing graphings
whose finite-cycle module is generated in propagation at most `L`, up to
dimension `o(1)` uniformly. This is the groupoid analogue of the fact that
the relation module of a finite presentation is generated by its relators.
For the Cayley graphing of a finitely presented group, `tau_L = 0` once
`L` is at least the maximal relator length. A controlled (propagation-L)
rank theory for `A` would be the needed new input. None is known.
