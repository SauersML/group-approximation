---
rg: 2
id: o2-zp-uct-witnesses-are-meager-and-perturbation-unstable
kind: claim
title: The Rokhlin class is a comeager conjugacy class among Z_p-actions on O_2, so every UCT witness set is meager, no perturbation-stable certificate can name a witness, and the prime half of Problem II is a closure statement
distinct_from:
  outer-actions-on-o2-kk-g-contractible-iff-rokhlin: that identifies the Rokhlin actions on O_2 with the KK^G-contractible outer actions and with one conjugacy class; this proves that class is a dense G_delta of the Polish space of all order-p actions and draws the category consequences for witnesses.
  bootstrap-zp-actions-realize-every-cyclotomic-k-module: that fences off certificates that factor through equivariant K-theory; this fences off certificates that are stable under point-norm perturbation of the action, a different class (topological, not K-theoretic).
  bernoulli-classes-meager-on-central-locally-finite-hosts: that is a category obstruction for Bernoulli isomorphism problems in measurable dynamics; this is the analogous obstruction for order-p automorphisms of O_2 and the UCT.
  o2-z2-actions-fix-a-cartan-subalgebra: that is the open Cartan-fixing statement at 2; this proves it generically and shows the open part is exactly a closure statement.
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

**ESTABLISHED (derivation, lane sw-085, 2026-09-17; unreviewed).**  Let `p` be
a prime and `Act_p` the set of order-`p` automorphisms `α` of `O_2` (actions
`Z_p ↷ O_2`) with the point-norm topology.  It is a Polish space, and
`Aut(O_2)` acts on it continuously by conjugation.  Write:

* `R_p`: actions with the Rokhlin property;
* `S_p`: strongly approximately inner actions (`α = lim Ad(u_n)`, `u_n ∈ O_2^α`
  unitary);
* `Out_p`: outer actions.

1. **Generic uniqueness.**  `R_p` is a dense G_δ in `Act_p` and a single
   conjugacy class (the class of the model `id ⊗ ⊗_n Ad(λ)` on
   `O_2 ⊗ M_(p^∞) ≅ O_2`).  `S_p` is a G_δ containing `R_p`.  So `S_p` is
   comeager: the question of Barlak--Li II Remark 4.14(2) has a positive answer
   for the generic action.
2. **Category dichotomy (no Baire-property hypothesis).**  A
   conjugation-invariant set `Y ⊆ Act_p` either contains `R_p` and is comeager,
   or is disjoint from `R_p` and is meager.  The same holds inside any subspace
   `X ⊇ R_p`.  Such an `X` (for instance `S_p ∩ Out_p`) is a Baire space in
   which `R_p` is a dense G_δ.
3. **Witnesses are meager.**  Each of these witness sets is conjugation
   invariant and disjoint from `R_p`, hence meager:
   - `W^UCT_p`: actions in `S_p ∩ Out_p` with `O_2 ⋊_α Z_p` not in the UCT
     class;
   - `W^Cart_p`: actions in `S_p ∩ Out_p` fixing no Cartan subalgebra (the
     Barlak--Li witnesses; `W^Cart_p = W^UCT_p` by Barlak--Li II Corollary 4.15);
   - `W^sai_p`: outer actions that are not strongly approximately inner;
   - `W^det_p`: outer actions with `O_2 ⋊_α Z_p ≃_KK 0` that are not Rokhlin (the
     detection witnesses of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`).
4. **No perturbation-stable certificate.**  Call `Q ⊆ X` a *stable certificate*
   if it is conjugation invariant and has nonempty interior in `X`: some action
   in `Q` has a finite set `F ⊂ O_2` and `ε > 0` such that every `β ∈ X` with
   `‖β(x) − α(x)‖ < ε` on `F` is in `Q`.  Every stable certificate contains a
   Rokhlin action, so it is contained in no witness set of item 3.  In
   particular, no test that reads an action through finitely many elements to
   finite precision can certify a UCT witness, a Cartan-free action, or a
   counterexample to Remark 4.14(2) or to detection.  This fails for
   topological reasons, not for lack of computing power.
5. **The 0-1 law cannot give emptiness.**  Let `N_p` be the set of outer
   actions that fix some Cartan subalgebra but are not Rokhlin.  It is
   conjugation invariant and meager, and every action in it has a UCT crossed
   product.  It is nonempty: the quasi-free action `λ_ζ(s_i) = ζ s_i`
   (`ζ = e^(2πi/p)`) fixes the diagonal `D_2`, and
   `K_0(O_2 ⋊_(λ_ζ) Z_p) ≅ Z/(2^p − 1) ≠ 0`, so it is outer and not Rokhlin.
   So being meager and invariant does not separate witnesses from
   non-witnesses, and no category argument upgrades item 3 to emptiness.
6. **The prime half is a closure statement.**  Let `X = S_p ∩ Out_p` and
   `C_p = {α ∈ X : α fixes a Cartan subalgebra}`.  Then `D_p` (every `α ∈ X`
   fixes a Cartan subalgebra; `o2-z2-actions-fix-a-cartan-subalgebra` at
   `p = 2`) holds iff `C_p` is closed in `X`.  More generally, a
   UCT-certificate `Φ ⊆ X` that holds on the Rokhlin model and is closed under
   point-norm limits inside `X` proves `D_p`.  So Problem II is equivalent to
   the existence of a limit-closed certificate at `p = 2` and at `p = 3`.
   Closure of the known certificates (invariant Cartan, equivariant bootstrap
   class, strong approximate innerness itself) fails at one step each time.  The
   witnessing data of `α_n` (a Cartan `D_n`, a `KK^G`-equivalence, implementing
   unitaries `u_n ∈ O_2^(α_n)`) is not controlled on any fixed finite set as `n`
   varies.

Proof: `o2-zp-uct-witnesses-are-meager-and-perturbation-unstable-proof`.

**What this kills.**  Negative side: Baire-generic, zero-one-law and
"random action" constructions of a witness, and every finite-precision search
over approximate data of an order-`p` automorphism of `O_2` (a witness is
never robust under perturbation).  Positive side: generic or almost-everywhere
arguments, which prove the comeager statement of item 3 and nothing more.  The
surviving positive shape is item 6: a certificate that passes to point-norm
limits.  Item 6 is a reformulation, not a strict simplification: both
directions hold, and the closure statement is not known to be easier than
`D_p`.
