---
rg: 2
id: leavitt-corner-toeplitz-support-class-is-jacobson-hyperlinearity
kind: claim
title: The Toeplitz-coefficient survivor class of the Leavitt BCS corner is exactly as hard as nonhyperlinearity of the Jacobson elementary group, and a single explicit Haar character decides it
distinct_from:
  leavitt-corner-bcs-support-coefficient-gate: that proves the gate and names complementary Toeplitz coefficients as the first survivor; this shows the survivor question is not a new question — a head-seeing hyperlinear quotient of E_20(T_2) exists iff EL_20(J) is hyperlinear — and it gives one explicit faithful character whose Connes-embeddability kills the whole class.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that proves the all-or-nothing alternative for EL_5(J); this reproves it for any group sandwiched between the finitary kernel and GL_n(J), applies it to the BCS corner support, and adds the Whitehead sandwich EL_20(J) <= GL_20(J) <= EL_40(J).
  binary-toeplitz-root-refinement-has-a-bernoulli-haar-fixed-point: that is a Bernoulli fixed point for a Schur-Toeplitz HNN; this is the fixed-point character of the Pontryagin-dual Haar action of GL_n(J) on its standard module.
---

**ESTABLISHED** (route `leavitt-corner-toeplitz-support-class-jacobson-proof`).

Notation.
- `R = L_(F_2)(1,2)` with `t_i s_j = delta_ij` and `s_1t_1 + s_2t_2 = 1`.
- `q = s_1t_1`, `z = x_13(q)`, `Delta = St_20(R)`, and `LNC3` as in
  `agent-leavitt-not-bcs-negative-root-corner`.
- `X` and `S_X` are as in `leavitt-corner-bcs-support-coefficient-gate`, and
  `T_2 = F_2<s_2,t_2>` is a subalgebra of `R`.
- `J = F_2<S,T | TS=1>`, `Q = 1-ST`, and `V = F_2^(N) (x) F_2^20` is the
  standard faithful `M_20(J)`-module.
- `L = GL_fin(V)` is the group of automorphisms `g` of `V` with `g-1` of finite
  rank, and `w = x_13(Q)`.

**(A) Coefficients.** `S |-> s_2`, `T |-> t_2` is an isomorphism `J -> T_2`
sending `Q` to `q`. So `E_20(T_2) = EL_20(J)` and `z = w`.

**(B) Monolith.** For every group `H` with `L <= H <= GL(V)`, every
homomorphism `phi` of `H` with `phi(w) != 1` is injective. This applies to
`H = EL_n(J)` and `H = GL_n(J)` for every `n >= 2`.

**(C) The need's question is hyperlinearity.** The following are equivalent:
- `E_20(T_2)` has a hyperlinear quotient in which `x_13(1-s_2t_2)` survives;
- `E_20(T_2)` has a homomorphism into `U(R^omega)` in which it survives;
- `EL_20(J)` is hyperlinear.

The Whitehead map `g |-> diag(g, g^(-1))` embeds `GL_20(J)` into `EL_40(J)`, so

```text
EL_20(J) <= GL_20(J) <= EL_40(J).                          (TJ1)
```

**(D) Class reduction.**
- If `EL_40(J)` is hyperlinear (or just `GL_20(J)`), no diagram `LNC3` has
  `S_X <= T_2`.
- If some `LNC3` has `S_X <= T_2`, then `GL_20(J)` and `EL_40(J)` are not
  hyperlinear.

**(E) One character decides the class.** Put

```text
tau(g) = 2^(-dim_F2 (g-1)V)   if g in L,
tau(g) = 0                    if g in GL_20(J) \ L.        (TJ2)
```

This is the fixed-point character `g |-> mu(Fix g)` of the Haar-preserving
dual action of `GL_20(J)` on the compact group `V^* = Hom(V, F_2)`.
- It is a faithful character with `tau(w) = 1/2`.
- If `LNC3` has `S_X <= T_2`, then `tau` is not Connes-embeddable: it
  would push forward to a Connes-embeddable tracial state on `A(B_loop)`
  with corner mass `tau(P_z) = 1/4`.
- Conversely, if `tau` is Connes-embeddable, the class is dead, and
  `GL_20(J)` is hyperlinear.

**(F) Where the natural attack on (E) dies.** Every sequence of
Hamming-asymptotic homomorphisms of `St_20(J)` by affine permutations of
finite `F_2`-spaces becomes eventually exact on a finite presentation, so it
factors through finite groups and moves `w` on a vanishing fraction of points.
- The invariant is that a non-identity affine map moves at least half of all
  points.
- The step where it dies is relator exactness on the finitely presented
  Steinberg cover.
- So periodic-point, truncation and finite-module shadows of the Haar action
  all give `tau(w) -> 1`, never `1/2`.
- Only non-affine (genuinely nonlinear) permutation models can witness `tau`.

**Impact.**
- The "next falsifiable step" of the target is not a new question. It is
  sandwiched by `(TJ1)` between hyperlinearity of `EL_20(J)` and of `EL_40(J)`.
- A Toeplitz-supported `LNC3` would make the Jacobson elementary groups
  nonhyperlinear. This is the same open endpoint that
  `binary-jacobson-el3-is-sofic` and the `property-t-free-existence-via-jacobson-*`
  gaps approach from the other side.
- The explicit character `(TJ2)` is a single test object: Connes-embeddability
  of the Haar character kills every Toeplitz-coefficient diagram at once.

**Parallel note (swarm-0917).** Another worker, `swarm-0917-w4-pull-nh-1`,
posted the monolith equivalence (C) on the bus at the same time, under the id
`toeplitz-supported-leavitt-corner-is-jacobson-hyperlinearity`. That version
applies it under the assumption `pi(X) <= EL_20(T_2)`.

The gate only gives `pi(Gamma_X) <= GL_20(T_2)`, and `GL_20(T_2)` need not be
contained in `EL_20(T_2)`. (D) closes that gap through the Whitehead sandwich
`(TJ1)`.

(E) and (F) are additional. The bus posting reports the Haar fixed-point
character only as a dead transplant. Here it is the single test object for the
class, with corner mass `1/4`, together with the exact affine step where its
algebraic models die.

When the orchestrator lands both nodes, it should merge them or add the pair to
`distinct_from`.
