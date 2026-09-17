---
rg: 2
id: sofic-fp-hard-for-every-finite-difference-level-proof
kind: route
title: Kill and collapse gadgets over Z edges realise every finite difference level inside nonsofic finite presentations
target: sofic-fp-hard-for-every-finite-difference-level
requires: [finitely-presented-nonsofic-group-exists, sofic-recognition-finite-presentations-arithmetical-position]
---

All presentations below are finite and are computed uniformly from their inputs.  "Sofic" facts used:

- (S1) Subgroups of sofic groups are sofic.  Free products of sofic groups are sofic.
- (S2) Residually finite groups and amenable groups are sofic.
- (S3) The fundamental group of a finite graph of groups with sofic vertex groups and amenable edge groups is
  sofic.  References: Elek-Szabo (Proc. AMS 2011) and Paunescu (JFA 2011) for amalgams over amenable
  subgroups; Collins-Dykema (Münster J. Math 2011) for HNN extensions; Ciobanu-Holt-Rees (Pacific J. Math
  271 (2014), arXiv:1212.2739) for general finite graphs of groups.

## 1. Seed release group

Let `D = <X | r_1, ..., r_m>` be the finitely presented nonsofic group of [[finitely-presented-nonsofic-group-exists]].
Let `Y = {y_1..y_m}` be new letters.  Define `phi` on `F(X u Y)` by `x -> x` and `y_i -> r_i y_i`.

**Lemma 1.**  `phi` is an automorphism.  `B_D = F(X u Y) x|_phi <z>` is finitely presented and sofic, `z` has
infinite order in it, and `B_D/<<z>> = D * F(Y)`.

*Proof.*
- `phi` is an automorphism.  Since `r_i in F(X)` is fixed by `phi`, the endomorphism `psi` with
  `y_i -> r_i^-1 y_i` inverts it.
- `B_D` is finitely presented.  Its presentation is `<X, Y, z | z x z^-1 = x, z y_i z^-1 = r_i y_i>`.
- `z` has infinite order.  `B_D` maps onto `Z` by `z -> 1` and `X u Y -> 0`.
- `B_D` is sofic.  Finitely generated free-by-cyclic groups are residually finite (G. Baumslag, "Finitely
  generated cyclic extensions of free groups are residually finite", Bull. Austral. Math. Soc. 5 (1971)); now
  apply (S2).
- The quotient.  Adding `z = 1` turns the relations into `x = x` and `y_i = r_i y_i`, that is `r_i = 1`.  So
  `B_D/<<z>> = <X, Y | r_1..r_m> = D * F(Y)`.  []

## 2. Machine edge

Fix a finitely presented solvable group `G(M) = <U | S>` that simulates a deterministic universal Minsky
machine `M`.  We use the Kharlampovich construction in the form of Kharlampovich-Myasnikov-Sapir
(arXiv:1204.6506, Section 4, Theorem 4.3; `G(M)` lies in `A_p^2 A`, so it is solvable, amenable and sofic).
Its property is:

- (M) There is a computable map `n -> c_n` from inputs to words in `U` such that `c_n = 1` in `G(M)` iff
  `M` accepts `n`.

In KMS, `c_n` is the configuration word `x_{q_1 A_0} a_1^n A_1 ... A_K`.  They show that it vanishes iff the
configuration is accepted.  The exact lemma number giving the direction "accepted implies trivial" is not
re-verified here; this is the citation tier of the proof.

Fix one accepted input `n_0` and put `w_n = c_n c_{n_0}^-1`.  Then `w_n = 1` iff `n` is accepted.  The accepted
set `A_M` is r.e.-complete.

Let `V_U = G(M) * <t>`.

**Lemma 2.**  If `w != 1` in `G(M)`, then `[w,t] = w t w^-1 t^-1` has infinite order in `V_U`.  If `w = 1`, then
`[w,t] = 1`.

*Proof.*  If `w != 1`, the word `w . t . w^-1 . t^-1` alternates between the two factors, with nontrivial
syllables, and is cyclically reduced of length 4.  Such elements of a free product have infinite order.  The
case `w = 1` is trivial.  []

## 3. Kill gadget

For a finite presentation `P` and a word `w` in `U`, let

```text
K(P,w) = P * ( B_D *_{ z = [w,t] } V_U ),
```

presented as the free product of the three presentations plus the one relation `z = [w,t]`.

**Lemma 3.**  `K(P,w)` is nonsofic iff `P` is nonsofic or `w = 1` in `G(M)`.

*Proof.*
- If `w != 1`: by Lemmas 1 and 2 both `<z>` and `<[w,t]>` are infinite cyclic.  So the relation defines a
  genuine amalgam `B_D *_Z V_U` of sofic groups over an amenable subgroup, which is sofic by (S3).  By (S1),
  `K(P,w)` is sofic iff `P` is sofic.
- If `w = 1`: then `[w,t] = 1`, and the relation reads `z = 1`.  So `K(P,w) = P * (B_D/<<z>>) * V_U =
  P * D * F(Y) * V_U` by Lemma 1.  This group contains `D`, so it is nonsofic by (S1).  []

## 4. Collapse gadget

Let `P = <g_1..g_k | R>`, and let `u_1..u_l` be the generators of `G(M)`.  Put `V_0 = P * <s>`.

- In `V_0` the elements `s, g_1 s, ..., g_k s` generate `V_0`, and each has infinite order.  For `g_j s`
  there are two cases: if `g_j = 1` it equals `s`; otherwise it is a cyclically reduced length-2 word of the
  free product.
- In `V_U` the elements `t, u_1 t, ..., u_l t` generate `V_U`, and each has infinite order, for the same
  reason.
- Call these `k+1+l+1` elements the *handles* `h`.

The graph of groups `C(P,w)` has these vertex groups:
- `V_0` and `V_U`;
- `BS_c = <y, c | c y c^-1 = y^2>`;
- for each handle `h`, a copy `BS_h = <y_h, h~ | y_h h~ y_h^-1 = h~^2>`.

It has these edges, each with edge group `Z` and each identifying two elements:
- (e1) `c in BS_c` with `[w,t] in V_U`;
- (e2) for each handle, `y in BS_c` with `y_h in BS_h`;
- (e3) for each handle, `h~ in BS_h` with `h` in `V_0` or `V_U`.

The group `C(P,w)` is the standard presentation of `pi_1`: the free product of the vertex presentations, one
stable letter `tau_e` for each edge outside a fixed maximal tree, and the relation `tau_e a tau_e^-1 = b` for
each edge (`tau_e = 1` on tree edges).  This is a finite presentation computed from `(P,w)`.

**Lemma 4.**  `C(P,w)` is nonsofic iff `P` is nonsofic and `w != 1` in `G(M)`.

*Proof.*
- If `w != 1`: every identified element has infinite order.
  - In `BS(1,2)`, the elements `y` and `c` have infinite order.
  - `[w,t]` has infinite order by Lemma 2.
  - The handles have infinite order by construction.
  So `C(P,w)` is a genuine finite graph of groups with edge groups `Z`, and its vertex groups embed.  The
  vertex groups `V_U` and `BS(1,2)` are sofic.  If `P` is sofic then `V_0` is sofic, and `C(P,w)` is sofic by
  (S3).  If `P` is nonsofic, then `C(P,w)` contains `V_0`, which contains `P`, so it is nonsofic.
- If `w = 1`: then `[w,t] = 1`.  Follow the relations in order.
  1. (e1) gives `c = 1` (a conjugate of `c` equals `1`, so `c = 1`), and then `y = y^2`, so `y = 1`.
  2. (e2) gives `y_h = 1` for every handle, and then `h~ = h~^2`, so `h~ = 1`.
  3. (e3) gives `h = 1` for every handle.
  4. The handles generate `V_0` and `V_U`, and each `BS` vertex is generated by its two now-trivial
     generators.  So every vertex group is trivial in `C(P,w)`.
  5. Every edge relation then reads `tau_e 1 tau_e^-1 = 1`, which is vacuous.
  So `C(P,w)` is the free group on the stable letters, which is sofic.  []

## 5. Difference levels

**Lemma 5 (Ershov normal form).**  A set `S` is `n`-c.e. iff `S = (A_1 - A_2) u (A_3 - A_4) u ...` for r.e.
sets `A_1 ⊇ A_2 ⊇ ... ⊇ A_n` (with `A_{n+1} = ∅`).  Indices for the `A_i` can be computed from an
`n`-c.e. index.

This is standard (Ershov 1968; Soare, *Recursively Enumerable Sets and Degrees*, Ch. III / Ex. on the
difference hierarchy).  One takes `A_i = {x : the approximation to S(x) changes at least i-1 times after
first becoming 1}`, suitably normalised.

Since `A_M` is r.e.-complete, there are computable `h_i` with `e in A_i` iff `M` accepts `h_i(e)`, that is,
iff `w_{h_i(e)} = 1`.

Define `P_0(e) = <|>`.  For `1 <= i <= n`, put `P_i(e) = K(P_{i-1}(e), w_{h_i(e)})` for `i` odd and
`P_i(e) = C(P_{i-1}(e), w_{h_i(e)})` for `i` even.

**Claim.**  `P_i(e)` is nonsofic iff `e in S_i`, where `S_0 = ∅` and
`S_i = S_{i-1} u A_i` (`i` odd), `S_i = S_{i-1} - A_i` (`i` even).
Moreover `S_i = (A_1 - A_2) u ... ` truncated at `i`.

*Proof.*  The first statement follows by induction from Lemmas 3 and 4.  For the normal form, use induction
and nestedness.
- For `i` odd, `S_{i-1} u A_i` is the truncated union with the new term `A_i`, since `A_i - A_{i+1}` will be
  cut later.
- For `i` even, `(T u A_{i-1}) - A_i = (T - A_i) u (A_{i-1} - A_i)`, where
  `T = (A_1 - A_2) u ... u (A_{i-3} - A_{i-2})`.
- Every term `A_{2j-1} - A_{2j}` of `T` has `2j <= i-2`, so `A_i ⊆ A_{2j}`, and subtracting `A_i` leaves it
  unchanged.  Hence `S_i = T u (A_{i-1} - A_i)`.  []

So `e -> P_n(e)` is a many-one reduction of `S` to `NONSOFIC_fp`, and it is uniform in the `n`-c.e. index.

**Omega-c.e.**  If `S` is omega-c.e. with computable change bound `f`, the same normal form holds with
`n = f(e)` computed from `e`, and one builds `P_{f(e)}(e)`.

## 6. Corollaries

- The difference hierarchy is proper: for each `n` there is a `D_n` set that is not co-`D_n`.
- If `NONSOFIC_fp` were in co-`D_n`, then every `D_n` set would be co-`D_n` (co-`D_n` is closed under
  many-one preimages).  That is impossible.
- Since `NONSOFIC_fp` is `D_{n+1}`-hard, and `D_n ⊆ co-D_{n+1}`, it is not `D_n` either.
- Hence neither `SOFIC_fp` nor `NONSOFIC_fp` lies in `BC(Sigma^0_1) = u_n (D_n u co-D_n)`.
- Case `n = 1`: `NONSOFIC_fp` is `Sigma^0_1`-hard, so `SOFIC_fp` is `Pi^0_1`-hard and not r.e.
- With [[sofic-recognition-finite-presentations-arithmetical-position]]:
  `SOFIC_fp in Pi^0_2 \ BC(Sigma^0_1)`.  []

## 7. Verification tier and known weak points

- The tier is a hand proof.  The imported theorems are (S3), Baumslag 1971 and KMS Theorem 4.3.
- Property (M) is used only as "some finitely presented sofic group has an r.e.-complete word problem via a
  computable family of words".  Any finitely presented amenable, or residually finite, group with an m-complete
  word problem can replace `G(M)`.
- A second source for (M) is Kharlampovich 1981 (solvable of class 3, simulating Minsky machines).
- Nothing depends on the rope or on [[sofic-safe-finite-presentation-compiler]].
