---
rg: 2
id: stably-finite-msg-rung-is-one-universal-algebra
kind: claim
title: The stably finite rung of the Kesten gap ladder is one statement in the universal stably finite quotient, it is Kazhdan whenever the maximal algebra is stably finite, and on a compressed subgroup it forces the quasi-regular algebra to be infinite
distinct_from:
  model-spectral-gap-quantifier-ladder: that decides rung 0 (all representations) by induction and records the stably finite rung as undecided because the induced representation is not tracial; this decides the stably finite rung, by collapsing it to one universal algebra, identifying it with rung 0 exactly when the maximal algebra is stably finite, and extracting a Kazhdan-free proper-isometry consequence when it is not.
  tracial-model-spectral-gap-is-character-gap-weaker-than-t: that decides the finite von Neumann rung through characters; this is the norm rung over all stably finite C-star targets, where no trace is assumed and the witness is a quasi-regular representation.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that proves (MSG) in the adjoint corona suffices for transport; this proves that (MSG) in any finite target already forces the transport equality there, and turns the manuscript proper-isometry argument into a per-algebra dichotomy that needs no (T).
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that studies the group-level kernel Rad_sf of all stably finite targets; this uses the C-star algebra those targets generate and asks about spectra in it, not about kernels.
  delta-e-adjoint-msg-is-fd-uniform-gap: that decides the model-generic corona rung by tensor saturation; this decides the rung of arbitrary stably finite targets, which contains the coronas and the reduced algebra.
artifacts:
  - research/stably-finite-msg-rung-is-one-universal-algebra-proof.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an
obstruction and a decomposition.  Notation follows
`kesten-spectral-gap-replaces-kazhdan-projection-per-model`.  `G` is
countable, `L<=G` is finitely generated, `S` is a finite symmetric
generating set of `L` with `e in S`, and `h_S=(1/|S|) sum_(s in S) u_s`.
`(MSG)` for `rho:G->U(A)` means that `1` is not an accumulation point of
`sp(rho(h_S))`.  The **stably finite rung** `SF(G,L)` is the statement
that `(MSG)` holds on `L` for every homomorphism of `G` into the unitary
group of a unital stably finite C-star algebra.  `FIN(G,L)` is the same
statement with "finite" in place of "stably finite".  The **compression
monoid** is `C_G(L)={t in G : tLt^-1 <= L}`.

1. **One universal algebra.**  Let `C*_SF(G)` be the completion of
   `C[G]` in the supremum of the norms of all such homomorphisms.  It is a
   unital stably finite C-star algebra, a quotient of `C*_max(G)`, and
   every homomorphism of `G` into a unital stably finite algebra factors
   through it.  The same holds for `C*_fin(G)` and finite targets.  Hence
   the following are equivalent:
   - (a) `SF(G,L)`;
   - (b) `(MSG)` on `L` in `C*_SF(G)`;
   - (c) there is `c>0` with `sp(rho(h_S)) cap (1-c,1)` empty for every
     stably finite target `rho`.

   The same equivalence holds for `FIN(G,L)` and `C*_fin(G)`.  The rung is
   a single spectral statement in one algebra, and it is automatically
   uniform.
2. **When the rung is Kazhdan.**  If `C*_max(G)` is stably finite (for
   example residually finite-dimensional, or MF), then `C*_SF(G)=C*_max(G)`
   and `SF(G,L)` holds if and only if `L` has property `(T)`.  The same is
   true of `FIN` when `C*_max(G)` is finite.
3. **Kazhdan-free proper-isometry dichotomy.**  Let `rho:G->U(A)` satisfy
   `(MSG)` on `L`, let `P=chi_{1}(rho(h_S))`, let `t in C_G(L)`, and put
   `u=rho(t)` and `q=uPu^*`.  Then `P<=q`, and `s=Pu^*+(1-q)` satisfies
   `s^*s=1` and `ss^*=1-(q-P)`.  So either `A` contains the proper
   isometry `s`, or in every representation `sigma` of `A`,
   ```text
   Fix sigma rho(L) = Fix sigma rho(t L t^-1) = Fix sigma rho(L^infty_t),
   L^infty_t = union_(k>=0) t^-k L t^k,
   ```
   and `Fix sigma rho(L)` is invariant under `sigma rho(t)`.
   Property `(T)` is used nowhere.  With `(T)` and `A=C*_max(G)` this is
   `prop:max-infinite` of `non_mf_groups_exist.tex`.
4. **The rung forces an infinite quasi-regular algebra.**  Suppose
   `t L t^-1` is a proper subgroup of `L`.  Let
   `A_q(G,L,t)=C*_(lambda_(G/tLt^-1))(G)` be the C-star algebra generated
   by the quasi-regular representation on `l^2(G/tLt^-1)`.
   - If `FIN(G,L)` holds, then `A_q(G,L,t)` is not finite.
   - If `SF(G,L)` holds, then `A_q(G,L,t)` is not stably finite.
   - Under `FIN(G,L)`, `C*_max(G)` is not finite.  Under `SF(G,L)`, it
     is not stably finite.  (This does not follow from the
     quasi-regular statement, since a quotient of a finite algebra can be
     infinite.  It is proved directly from item 3 in `C*_max(G)`.)

   More generally, under `FIN(G,L)` no representation of `G` that factors
   through a finite algebra has a vector fixed by `tLt^-1` but not by `L`.

## The class it kills, and the invariant

Item 2 extends the rung-0 obstruction of
`model-spectral-gap-quantifier-ladder` to the stably finite rung, for
every ambient group whose maximal algebra is stably finite.  An argument
for `SF(G,L)` valid for every `(G,L)` in a class that contains one pair
with `C*_max(G)` stably finite and `L` without `(T)` is wrong.  Examples
are `(F_2,F_2)` and `(BS(1,2),<a>)`, where the rung fails outright.  If
the argument is valid only on pairs with `C*_max(G)` stably finite, it is
a Kazhdan theorem.

Item 4 says what is left for the others: a proof of `SF(G,L)` for a
strictly compressed `L` contains a proof that the quasi-regular algebra of
the compression has a proper isometry in some matrix algebra.  The
invariant is the stable finiteness of `C*_max(G)`, or of the quasi-regular
algebra `A_q(G,L,t)`.  The step where a Kazhdan-free argument dies is the
production of that proper isometry.  In the manuscript the only source of
it is the Kazhdan projection (`prop:max-infinite`).  Rank-free or
trace-free positivity arguments cannot produce it:
- `lambda_G` is a stably finite target in which the fixed spaces of
  every infinite subgroup are `0`, so the dichotomy is trivially on the
  equality side;
- tracial targets see only characters
  (`tracial-model-spectral-gap-is-character-gap-weaker-than-t`).

## Consequence for the Leavitt goal

For `Delta=St_20(L_(F_2)(1,2))`, the subgroups `L` and `K` that the
manuscript uses are covered.  By items 1 and 3 of
`kesten-spectral-gap-replaces-kazhdan-projection-per-model`, `SF(Delta,L)`
and `SF(Delta,K)` imply the transport and normal-subgroup theorems.  The
reason is that the adjoint corona and the norm coronas are stably finite
targets.  So `SF` is a genuine prerequisite of the endpoint, stated in one
algebra `C*_SF(Delta)`.

The rank-four compression is strict.  In the manuscript's words, "the
compression is strict, since `e(sat)=0` while `e.1=e!=0` puts `e_12(1)` in
`L\uLu^-1`" (`non_mf_groups_exist.tex`, proof of the ring-compression
corollary, just before its application of `prop:max-infinite` to
`L<=EL_n(R)`).  Write `E=EL_20(L_(F_2)(1,2))`, a quotient of `Delta`.
Every stably finite target of `E` is one of `Delta`, and the lifted
subgroup maps onto `L`.  So `SF(Delta, lift of L)` implies `SF(E,L)`.
By item 4, a Property-`(T)`-free proof of it must in particular prove,
without `(T)`, that `A_q(E,L,u)` and `C*_max(E)` are not stably finite.  This is a
necessary sub-prerequisite that can fail independently.  No Kazhdan-free
proof of it is known in the graph.  For Thompson's `V`, the open question
"is `C*_max(V)` stably finite?" of the wave-14 attempt now has a sharp
reading: if it is, then `SF(V,L)` holds only for finite `L`.

Proof route: `stably-finite-msg-rung-is-one-universal-algebra-proof`.
