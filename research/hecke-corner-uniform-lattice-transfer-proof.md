---
rg: 2
id: hecke-corner-uniform-lattice-transfer-proof
kind: route
title: Restrict the permutation representation to the lattice and read the trace at orbit representatives
target: hecke-corner-uniform-lattice-transfers-embeddability
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
---

**Conventions.**
- The regular representations on `l^2(Gamma)` are
  `lambda(g) delta_s = delta_(gs)` and `rho(g) delta_s = delta_(s g^(-1))`.
- `R(Gamma) = rho(Gamma)''`.  By the commutation theorem for group von
  Neumann algebras, `lambda(Gamma)' = R(Gamma)` (standard).
- `tau_Gamma(y) = <y delta_e, delta_e>` is a faithful normal tracial state on
  `R(Gamma)`.
- The unitary `W delta_s = delta_(s^(-1))` satisfies
  `W rho(g) W* = lambda(g)`.  So `R(Gamma)` is spatially isomorphic to
  `L(Gamma)`, preserving `tau_Gamma`.
- For a finite subgroup `F`, put `e_F = |F|^(-1) sum_(f in F) rho(f)`.  It is a
  projection in `R(Gamma)` with `tau_Gamma(e_F) = 1/|F|`.

**Step 1: orbit decomposition.**  `l^2 X` is the direct sum of the spaces
`l^2(Gamma x_i)`, and `gamma F_i -> gamma x_i` identifies `Gamma x_i` with
`Gamma/F_i`.  Define

```text
V_i : l^2(Gamma/F_i) -> e_(F_i) l^2(Gamma),
V_i delta_(s F_i) = |F_i|^(-1/2) sum_(t in s F_i) delta_t.            (HT1)
```

- Distinct cosets give orthogonal unit vectors.
- Their span is the space of right-`F_i`-invariant vectors, which is the range
  of `e_(F_i)`.
- `lambda(g) V_i delta_(sF_i) = V_i delta_(g s F_i)`.

So `V = (+)_i V_i` is a unitary from `l^2 X` onto
`Q (l^2(Gamma) (x) C^m)`, where `Q = diag(e_(F_1), ..., e_(F_m))`.  It
intertwines `pi|Gamma` with the restriction of `lambda (x) 1_m`.

**Step 2: the corner.**  Two elementary facts about commutants:
- `(lambda(Gamma) (x) 1_m)' = M_m(lambda(Gamma)') = M_m(R(Gamma))`: a matrix
  commutes with a diagonal family exactly when its entries do.
- `Q` lies in that commutant, so the commutant of the subrepresentation on the
  range of `Q` is `Q M_m(R(Gamma)) Q`.

Since `Gamma <= G`, `M = pi(G)' <= pi(Gamma)'`, and

```text
Phi(T) = V T V*   lies in   Q M_m(R(Gamma)) Q.                      (HT2)
```

`Phi` is spatial, hence a unital, injective, normal *-homomorphism into the
corner (unital meaning `Phi(1) = Q`).  Composing with `W` gives values in
`Q' M_m(L(Gamma)) Q'`, where `Q' = diag(W e_(F_i) W*)`.

**Step 3: the trace constant.**  Let `T` be in `M`.  The diagonal entry
`Phi(T)_(ii)` lies in `e_(F_i) R(Gamma) e_(F_i)`.  By (HT1),
`e_(F_i) delta_e = |F_i|^(-1/2) V_i delta_(F_i)`, which corresponds to
`|F_i|^(-1/2) delta_(x_i)`.  Hence

```text
tau_Gamma(Phi(T)_(ii)) = <Phi(T)_(ii) e_(F_i) delta_e, e_(F_i) delta_e>
                       = |F_i|^(-1) <T delta_(x_i), delta_(x_i)>.        (HT3)
```

`G` is transitive, so `delta_(x_i) = pi(g_i) delta_(x_0)` for some `g_i`.
Because `T` commutes with `pi(g_i)`,

```text
<T delta_(x_i), delta_(x_i)> = <T delta_(x_0), delta_(x_0)> = tau(T).
```

Summing over `i` gives (HC1).

**Step 4: tau is a faithful normal trace.**  `Tr_m (x) tau_Gamma` is a
faithful normal trace on `M_m(R(Gamma))`, with value `sum_i 1/|F_i| = c` on
`Q`.  So `t = c^(-1) (Tr_m (x) tau_Gamma)` is a faithful normal tracial state
on the corner.  By Step 3, `tau = t o Phi`, and `Phi` is an injective normal
*-homomorphism.  Hence `tau` is a faithful normal tracial state on `M`.

**Step 5: corners of amplifications stay Connes-embeddable.**  Let `(N, tau_N)`
embed trace-preservingly into a tracial ultraproduct
`prod_U M_(d_n)`.  Then:
- `M_m(N)`, with trace `tr_m (x) tau_N`, embeds into
  `M_m(prod_U M_(d_n)) = prod_U M_(m d_n)`.  Representing sequences can be taken
  entrywise, and the 2-norms agree.
- Let `Q` be a projection in `M_m(N)` with trace `s > 0`.  Choose self-adjoint
  contractions `y_n` representing it, and let `Q_n` be the spectral projection
  of `y_n` on `[1/2, 1]`.  Then `||Q_n - y_n||_2 -> 0`, so `(Q_n)` also
  represents `Q`, and `tr(Q_n) -> s`.
- Hence `Q M_m(N) Q` sits inside `prod_U Q_n M_(m d_n) Q_n`, with normalized
  traces `tr / tr(Q_n)` converging to `s^(-1)` times the trace, and
  `Q_n M_(m d_n) Q_n = M_(rank Q_n)`.

So the corner, with its normalized trace, is Connes-embeddable.

**Step 6: (HC2).**
- If `Gamma` is hyperlinear, `L(Gamma)` is Connes-embeddable by direction (1)
  ⟹ (2) of `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`.
- By Step 5 the corner `Q' M_m(L(Gamma)) Q'` with trace `t` is
  Connes-embeddable.
- By Steps 3 and 4, `(M, tau)` embeds into it trace-preservingly.
- Composing with a unital *-homomorphism `rho : A -> M` gives an embeddable
  realization of `tau o rho`.

**Step 7: (HC3).**
- **Finite stabilizers.**  The stabilizer of `gK` in `Gamma` is
  `Gamma ∩ g K g^(-1)`, a discrete subgroup of a compact group, hence finite.
- **Finitely many orbits.**  Each double coset `Gamma g K` is open, because
  `K` is open.  These double cosets partition `G` into disjoint left-`Gamma`-invariant
  open sets, so they give a disjoint open cover of the compact space `Gamma\G`.
  Such a cover is finite.
- **Transitivity.**  `G` acts transitively on `G/K`.

**Step 8: (HC4) and (HC5).**  (HC4) is (HC2) applied to the hyperlinear lattice.

For (HC5):
- **The tree.**  The Cayley graph of `W_a` with respect to its `a` involutive
  generators `s_i`, with edges `{w, w s_i}`, is the `a`-regular tree.  Every
  vertex has degree `a`, the graph is connected, and a closed path without
  backtracking would spell a nontrivial reduced word equal to `e`.  That is
  excluded by the normal form theorem for free products.
- **The lattice.**  Left multiplication makes `W_a` act freely and transitively
  on vertices.  A vertex stabilizer `S_v` in `Aut(T_a)` is compact open, so
  `W_a ∩ S_v = 1` makes `W_a` discrete.  Also `Aut(T_a) = W_a S_v`, so `W_a\Aut(T_a)`
  is an image of `S_v`, hence compact.  The same holds for the product and for
  `S_v x S_w` in `Aut(T_a) x Aut(T_b)`, and for every closed subgroup containing
  `W_a x W_b`, where the quotient is closed in a compact space.
- **Hyperlinearity of `W_a`.**  `W_a` is the fundamental group of a finite
  tree of groups with vertex groups `Z/2` and trivial edge groups.  So it is
  hyperlinear by (AEG1) of `amenable-edge-graph-corners-cannot-groupify-a-nonce-game`.
- **Hyperlinearity of the product.**  If `U_n` and `V_n` are microstates for
  `W_a` and `W_b` (direction (1) ⟹ (3) of the dictionary node), then
  `U_n(g) (x) V_n(h)` are microstates for `W_a x W_b`.  The normalized
  Hilbert--Schmidt norm is multiplicative on tensors of unitaries, so the
  multiplicativity defect is at most the sum of the two defects, and the traces
  multiply to `delta_((g,h),e)`.  By (3) ⟹ (1), `W_a x W_b` is hyperlinear.

Now (HC4) applies.  The Burger--Mozes and Radu lattices are uniform lattices in
`Aut(T_a) x Aut(T_b)`, because they act properly and cocompactly on
`T_a x T_b`.
