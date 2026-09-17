---
rg: 2
id: deligne-sector-eigenvector-certificates-die-at-induction
kind: claim
title: Invariant-vector, vector-state-atom and Kazhdan-corner certificates for Deligne sector emptiness are either circular or refuted by an induced character
distinct_from:
  deligne-sector-siegel-spectrum-is-full-torus: that kills certificates through non-full or non-Haar Siegel spectrum and lists vector-state atoms, invariant vectors and relative-(T) corners as survivors; this kills exactly those survivors at their state-level step, for every subgroup of the cover.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is the open gate; this is a no-go about one class of proofs of it and decides nothing about the gate.
  augmentation-lifting-equals-full-mf-radical: that shows one C-star lifting criterion is equivalent to its conclusion for groups without finite-dimensional representations; this shows a Magee--de la Salle-type two-step certificate is circular or false over a Deligne fibre.
  mdls-obstruction-is-affine-mechanism-plus-level-matching: that analyses where the Magee--de la Salle invariant vector comes from in congruence quotients; this is about the refutation step, which over a nontrivial Maslov fibre can never be state-level.
---

**ESTABLISHED (class-kill).**  Route
`deligne-sector-eigenvector-certificates-die-at-induction-proof`.

**Setting.**  `E_3` is Deligne's triple cover of `Sp_4(Z)`, `z` generates its
order-three kernel, `omega = e^(2 pi i/3)`, and
`A_omega = C*(E_3)/(z - omega)`.  A **sector model** is a sequence
`sigma_n : E_3 -> U(d_n)`, `d_n >= 1`, with
`||sigma_n(gh) - sigma_n(g) sigma_n(h)|| -> 0` for all `g, h` and
`||sigma_n(z) - omega I|| -> 0`.  (Composing an `alpha`-projective tuple with
a set-theoretic section, `sigma(s(g) z^j) = omega^j sigma(g)`, turns the
tuples of `deligne-nontrivial-maslov-opnorm-sectors-are-empty` into sector
models, and back.  The `alpha^2` sector is the same after `omega -> omega^2`.)

Let `K <= E_3` be a subgroup containing `z`.  An **eigenline certificate at
`K`** is a proof of sector emptiness in two steps:

- **(V1)** every sector model has **asymptotic eigenlines** for `K`: unit
  vectors `xi_n` and scalars `lambda_n(k)` with
  `||sigma_n(k) xi_n - lambda_n(k) xi_n|| -> 0` for every `k in K`, along
  some subsequence;
- **(V2)** no state `phi` of `A_omega` and character `chi : K -> T` satisfy
  `phi(u_k) = chi(k)` for all `k in K`.

The **Kazhdan-corner** variant replaces (V2) by: **(V2c)** a projection
`q in A_omega`, which in every representation projects onto the
`chi`-eigenspace of `K` for a fixed character `chi`, is zero.

**Theorem.**

1. *Limits are characters.*  If a sector model has asymptotic eigenlines for
   `K`, then along an ultrafilter `lambda = lim lambda_n` is a character of
   `K` with `lambda(z) = omega`.  The limit vector state is a state `phi` of
   `A_omega` with `phi(u_k) = lambda(k)`.
2. *Circular branch.*  If `K` has no character `chi` with `chi(z) = omega`,
   then no sector model has asymptotic eigenlines for `K`.  So (V1) at `K`
   is equivalent to sector emptiness: the certificate assumes its
   conclusion.
3. *Refuted branch.*  If `chi : K -> T` is a character with `chi(z) = omega`,
   then the induced representation `Ind_K^(E_3) chi` factors through
   `A_omega` and has a unit `chi`-eigenvector for `K`.  So (V2) is false for
   `(K, chi)`, and so is (V2c) for every projection `q` as in its
   hypothesis.
4. *Hence* every eigenline or Kazhdan-corner certificate, at every subgroup
   `K` of `E_3`, either assumes sector emptiness in (V1) or fails at
   (V2)/(V2c).  By
   `deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`, branch 3 applies
   to `K = p^(-1)(H)` for `H` any subgroup of `SL_2(Z) x SL_2(Z)`, `P_S(Z)`
   or `P_K(Z)`.  This covers the Siegel radical `Sym_2(Z) = Z^3`, the
   Klingen Heisenberg radical, every `SL_2(Z)` block and every Levi factor.
   In particular it covers the survivors "vector-state atoms" and
   "relative-(T) corners" recorded in `deligne-sector-siegel-spectrum-is-full-torus`.

**Invariant and step of death.**  The invariant is the pair `(K, chi)`,
that is, the class of `alpha|_(p(K))` in `H^2(p(K); T)`.  If the class is
nonzero, (V1) is vacuous-circular.  If it is zero, the induced
representation `Ind_K^(E_3) chi` lives in the fibre and kills the refutation
step.

**What survives.**  A Magee--de la Salle-type proof over a nontrivial Maslov
fibre must use the finite dimension of the model in the refutation step as
well as in (V1).  It cannot pass through any state, projection or
representation of `A_omega`, because the induced representation supplies all
of them.  Such a proof would have to use, for example, the rank of the
eigenline range relative to `d_n`, or an interaction between two asymptotic
eigenspaces that no infinite-dimensional representation can reproduce.
This is the "matrix origin of models" survivor, now the only one.

DERIVATION
deligne-sector-eigenvector-certificates-die-at-induction-proof
