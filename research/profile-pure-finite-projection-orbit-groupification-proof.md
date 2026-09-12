---
rg: 2
id: profile-pure-finite-projection-orbit-groupification-proof
kind: route
title: Quotient the stabilizer of one profile-pure projection and induce over its formal coset blocks
target: profile-pure-finite-projection-orbit-groupifies-zpc-gap
requires: []
---

Let `E_l` be a joint readable selector and let `c` be a controlled affine row
active at `l`, after the readable signs have been substituted. The ZPC
same-question and supported-edge commutators make `c` an involution commuting
with `E_l`. The losing projection is

```text
E_l(1-pi(c))/2.                                         (PPP1)
```

Perfectness and faithfulness of the normalized negative-corner trace make
`(PPP1)` zero. Hence

```text
E_l pi(c)=E_l.                                          (PPP2)
```

If `p_t<=E_(r(t))` and `c=c_(t,a)` is active at `r(t)`, then `(PPP2)` gives

```text
p_t pi(c)=p_t.
```

Taking adjoints and using unitarity gives `pi(c)p_t=p_t`; therefore `c`
fixes `p_t` under conjugation. Consequently
`h_(t,a)=x_t^(-1)c_(t,a)x_t` belongs to `H`.

The action of `Q_G` on the finite set `T` is transitive by definition, and
orbit--stabilizer gives

```text
Q_G/H ~= T.                                             (PPP3)
```

This uses equality of the conjugate projections as operators, not
orthogonality of their ranges. In particular `[Q_G:H]=|T|<infinity`.
Because `Q_G` is finitely presented, Reidemeister--Schreier makes `H`
finitely presented.

Every `h in H` commutes with `p_0`, so

```text
sigma_0(h)=p_0 pi(h)p_0                                 (PPP4)
```

is a unitary representation of `H` in the finite tracial corner
`p_0Mp_0`. Conjugating the preceding row identity by `x_t^(-1)` shows that
`sigma_0(h_(t,a))=p_0`; thus `(PPP4)` factors through `K_T`. Centrality of
`J` makes it fix `p_0`, so `J in H`, while `p_0<=q_-` gives

```text
sigma_0(J)=-p_0.                                        (PPP5)
```

It follows that the image `bar J` is central and nontrivial in `K_T`.
There are only finitely many orbit points and verifier rows, so `(PPO5)`
adds finitely many relators and `K_T` is finitely presented.

Suppose for contradiction that `K_T` is hyperlinear. In `L(K_T)` put

```text
e_-=(1-lambda(bar J))/2,
A=e_-L(K_T)e_-.
```

The normalized corner `(A,tau_A)` is Connes embeddable, and

```text
sigma(h)=e_-lambda(bar h),       h in H,                (PPP6)
```

is a unital representation which sends `J` to `-e_-` and kills every
`h_(t,a)`.

Choose the representatives `x_tH` from `(PPP3)`. For `g in Q_G` define

```text
kappa(g,t)=x_(gt)^(-1) g x_t in H,
V_g(e_t tensor xi)=e_(gt) tensor sigma(kappa(g,t))xi.    (PPP7)
```

The cocycle identity for `kappa` makes `V` a representation of `Q_G` in
`M_|T|(A)`. Define each readable involution diagonally on these newly
constructed blocks by

```text
R_i(e_t tensor xi)=(-1)^(r_i(t))e_t tensor xi.           (PPP8)
```

These formal coset blocks are mutually orthogonal by construction. They are
not the physical ranges of the projections `p_t`, so possible overlaps
`p_t p_s!=0` play no role.

All unreadable relations hold because `V` is a representation of `Q_G`.
For every mixed commutator required by the game, the corresponding
unreadable generator `u` commutes in the source strategy with the relevant
readable spectral projection. Thus

```text
p_t<=E_(r_i(t))
  implies pi(u)p_tpi(u)^*<=E_(r_i(t)).                  (PPP9)
```

Profile purity of the target projection `p_(ut)` forces
`r_i(ut)=r_i(t)`, which is exactly `R_iV_u=V_uR_i` in `(PPP7)--(PPP8)`.
If `c_(t,a)` is active on block `t`, then it fixes `p_t`, and

```text
kappa(c_(t,a),t)=h_(t,a).
```

Hence `V_(c_(t,a))` is the identity on that block. Finally `J` acts
trivially on `T`, and `(PPP6)` gives `V_J=-1` on every block. Therefore the
constructed tuple satisfies every question PVM relation, every required ZPC
commutator, and every controlled verifier row.

The normalized trace on `M_|T|(A)` is a perfect Connes-embeddable tracial
strategy for `G`. Lifting its finitely many question PVMs to exact matrix
PVMs in a tracial matrix ultraproduct gives finite-dimensional quantum
strategies whose losses tend to zero. Thus `omega*(G)=1`, contradicting
`(PPO1)`. Therefore `K_T` is nonhyperlinear.

No sum of the source projections is used. In particular the proof requires
neither orthogonality of `T` nor centrality in `M` of any orbit sum: only the
abstract finite `Q_G`-set in `(PPP3)` enters the induction.
