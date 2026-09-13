---
rg: 2
id: twisted-brin-thompson-wp-equals-actor-orbit-problem-proof
kind: route
title: Track one brick through the word, resolving coordinate equalities by stabilizer-membership queries
target: twisted-brin-thompson-wp-equals-actor-orbit-problem
requires: [twisted-btb-clopen-action-is-type-a, twisted-brin-thompson-finite-presentation-criterion, fp-simple-highly-transitive-groups-satisfy-pbh]
---

Notation is the brick calculus of `twisted-btb-clopen-action-is-type-a`.
- A brick is `B(u)` for finitely supported `u : S -> {0,1}^*`.
- `h_u` is prefix insertion.
- `(tau_g kappa)(s) = kappa(g^-1 s)`.
- Branches are `h_v tau_g h_u^-1 : B(u) -> B(v)`.

Two identities are used throughout:

```text
tau_g h_u = h_(g.u) tau_g,   (g.u)(t) = u(g^-1 t);     h_v h_w = h_(v*w),   (TP1)
```

where `(v*w)(t)` is the concatenation `v(t)w(t)`.

**Branch identity test.** A branch `h_v tau_g h_u^-1` is the identity on `B(u)`
iff `g = 1` in `G` and `u = v`.
- *If `g != 1`:* faithfulness gives `t` with `g^-1 t = t' != t`. Output
  coordinate `t` is `v(t)` followed by the stripped input coordinate `t'`. Inside
  `B(u)` that input varies independently of input coordinate `t`, so the branch
  is not the identity.
- *If `g = 1`:* `u(t)w = v(t)w` for all infinite words `w` forces `u(t) = v(t)`.

This is the argument of `regular-cyclic-twisted-core-proof`, with an arbitrary
actor in place of `Z`.

## (a) Lower bound

`G` is the subgroup of single-branch elements `tau_g`. Rewriting `X` over any
finite generating set of `SV_G` costs a constant factor.

For `(TBO1)`, let `x, y` be elements with all branches supported in `{r_i}` and
trivial labels, i.e. elements of the copy of `V` on coordinate `r_i`, chosen with
`[x,y] != 1`. By `(TP1)`, `tau_u x tau_u^-1` has the same branches with supports
moved to `{u r_i}` and the same prefixes.
- If `u r_i != r_i`, it acts on coordinate `u r_i` alone and `y` on `r_i` alone.
  Elements acting on disjoint coordinates commute, so the commutator is `1`.
- If `u r_i = r_i`, it equals `x`, and the commutator is `[x,y] != 1`.

The word `[tau_u x tau_u^-1, y]` has length `2|u| + O(1)`, so this is a
linear-time reduction with one negated query.

## (b) Upper bound

**Fixed data.** A finite generating set `Sigma` of `SV_G`, closed under inverses.
Each `sigma in Sigma` is a finite list of branches `(u, g, v)` with `g` a fixed
word over `X`. Let:
- `D ⊆ S` be the union of all supports occurring (finite);
- `p` bound all prefix lengths and `L` all label lengths;
- for `d in D`, `e_d` be a word over `X` with `d = e_d r_(i(d))`.

**Symbolic coordinates.** Represent a point of `S` by a pair `(w, i)`, meaning
`w r_i`. Then `(w,i) = (w',i')` iff `i = i'` and `w'^-1 w in Stab_G(r_i)`. That is
one `OP` query on a word of length `|w| + |w'|`.

**State.** A triple `(u, gamma, v)`. Here `u` and `v` are finite tables of
symbolic coordinates with binary words, and `gamma` is a word over `X`. The state
means that the suffix read so far acts on `B(u)` as `h_v tau_gamma h_u^-1`. Start
from `(empty, empty word, empty)`.

**Reading a letter.** Read `sigma` (the letter to the left of the suffix). For
each `d in D`, look up `d` among the coordinates of `v` by `OP` queries.
- **Refine.** While `|v(d)| < p`, branch on a digit `a in {0,1}`. Append `a` to
  `v(d)`, and also to `u` at the original coordinate `gamma^-1 d = (gamma^-1 e_d, i(d))`,
  located among the coordinates of `u` by `OP` queries. On the sub-brick where the
  input has that digit, the same branch formula holds with the longer prefixes.
- **Select.** Once every `|v(d)| >= p`, exactly one branch `(u_s, g, v_s)` of
  `sigma` has `B(v) ⊆ B(u_s)`, found by comparing prefixes on `D`.
- **Compose.** Write `v = u_s * w`. By `(TP1)`,
  `h_(v_s) tau_g h_(u_s)^-1 h_v tau_gamma h_u^-1 = h_(v_s * g.w) tau_(g gamma) h_u^-1`.
  The coordinates of `g.w` are the pairs `(g c, i)` for coordinates `(c,i)` of
  `w`. Merging them with `v_s` needs `OP` queries.

**Accept.** At a leaf with state `(u, gamma, v)`, accept iff `gamma = 1` in `G`
(one `OP` query) and `u = v` after identifying coordinates (`OP` queries). The
word is trivial iff every leaf accepts: the leaf bricks partition the cube, and
the branch test above applies to each.

**Cost.** Each letter appends at most `|D|p` digits, so a leaf is determined by at
most `|D|p*l` binary choices, giving at most `2^(|D|p*l)` leaves. Along a path:
- tables have `O(|D| l)` entries;
- words have length `O(L l)`;
- there are `O(|D|^2 l^2)` queries, each of length `O(L l)`, plus polynomial
  bookkeeping.

The total is `2^(c l) (T(c l) + 1)` for a suitable `c`, which is `(TBO2)`. A single
path is a polynomial-size nontriviality witness when some leaf rejects.

## (c) Classes

- *Upper transfer.* If `T(n) = C g(Cn) + Cn + C` with `g` non-decreasing, then
  `2^(cn)(T(cn)+1) <= C' g*(C'n) + C'n + C'` with `C' = cC + c + 1`.
- *Lower transfer.* `F(g)` is closed under the length-linear substitution of (a)
  and under complement. So an algorithm for `SV_G` in `F(g)` would put `OP(G,S)`
  in `F(g)`.

## (d) Equivalences

- *1 => 2.* Word problem instances are part of `OP`.
- *2 => 3.* Given `T`, let `T+(m) = m + max_(k<=m) T(k)`, take an action with
  `OP(G,S)` outside `F(T+)`, and apply (c). `SV_G` is finitely presented by
  `twisted-brin-thompson-finite-presentation-criterion`.
- *3 => 1.* A finitely presented `SV_G` has a faithful type (A) actor `G`, so
  `twisted-btb-clopen-action-is-type-a` applies. It makes `SV_G` itself a faithful
  type (A) actor on the clopen sets of its cube, with the same word problem.
- *3 => 4.* A finitely presented `SV_G` satisfies (ii) of Theorem C in
  `fp-simple-highly-transitive-groups-satisfy-pbh`, trivially, so it embeds in a
  finitely presented simple highly transitive group `H`. Substitution gives
  `WP(SV_G) <= WP(H)` in the sense of (c), so `H` is outside `F(T)` whenever
  `SV_G` is outside `F(T+)`. Every highly transitive finitely generated simple
  group is MIF; under 4 either adjective may be chosen, since (iii) and (iv) of
  Theorem C are equivalent.
- *4 => 1.* A finitely presented simple MIF (or highly transitive) group `Γ`
  satisfies (iv) (or (iii)) of Theorem C, hence (i): `Γ <= G` for some `G` with a
  type (A) action. After passing to the faithful image, the action stays of
  type (A). Substitution gives `WP(Γ) <= WP(G)`.

  The faithful image needs one check. Theorem C's (i) uses Zaremsky's type (A),
  which includes faithfulness, as quoted in
  `type-a-action-gives-boone-higman-for-subgroups`, so no quotient is needed.

**Iteration.** The clopen stabilizer membership test, `f(U) = U` for a clopen `U`
given as a finite union of bricks, runs the same brick tracking on the bricks of
`U`. So `OP(SV_G, clopen sets)` obeys `(TBO2)` as well. `∎`
