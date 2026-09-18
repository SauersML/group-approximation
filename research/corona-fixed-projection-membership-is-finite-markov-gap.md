---
rg: 2
id: corona-fixed-projection-membership-is-finite-markov-gap
kind: claim
title: The fixed-vector projection of any subgroup lies in the adjoint corona only when one finite Markov element of the subgroup has an isolated eigenvalue at 1, so no non-group element of the corona can supply a transport projection
distinct_from:
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that shows (MSG) for a finitely generated L places P in C*(rho(L)) and suffices for transport; this proves the converse for an arbitrary countable subgroup, possibly infinitely generated or locally finite, by ultraproduct saturation - P_L in B forces (MSG) for a finite subset F with Fix(F)=Fix(L), so P_L already lies in C*(sigma~(<F>)).
  model-spectral-gap-quantifier-ladder: that shows representation-generic proofs of (MSG) are Kazhdan theorems; this shows that membership of P_L in the whole corona B, not only in the group-generated algebra, is (MSG) for a finite subset, so a transport projection obtained from any element of B is still a finite Markov spectral gap.
  root-column-fixed-projection-is-not-in-root-pair-cstar: that excludes P_N from C*(sigma~(K)) and leaves open P_N in B through non-group elements; this closes that escape in general, since P_N in B implies P_N in C*(sigma~(N)).
  window-average-kazhdan-substitute-forces-trivial-corona-rep: that kills norm limits of window averages; this identifies the only way P_L can be in B at all.
artifacts:
  - research/corona-fixed-projection-membership-is-finite-markov-gap-proof.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED (written proof; not Lean-verified).**

**Setting** (that of Theorem `thm:transport` of `non_mf_groups_exist.tex`).
- `G` is countable, `(V_n)` is an operator-norm asymptotic representation of
  `G` on `C^(d_n)`, and `sigma~(g)=[Ad V_n(g)]` in the adjoint corona
  `B=prod_n B(M_(d_n)(C),||.||_2)/direct_sum`.
- For a free ultrafilter `omega`, `H_omega` is the ultraproduct of the
  Hilbert spaces `(M_(d_n)(C),||.||_2)` and `pi_omega` the representation of `B`
  on it. `H_B=direct_sum_omega H_omega` over all free ultrafilters, with
  `pi=direct_sum pi_omega` (faithful).
- For `L<=G`, `P_L` is the projection of `H_B` onto `Fix pi(sigma~(L))`.
  For finite symmetric `F subset L`, `h_F=(1/|F|) sum_(f in F) sigma~(f)`,
  a self-adjoint contraction in `B`.

**Theorem (corona saturation).** For every subgroup `L<=G` the following are
equivalent:
1. `P_L in pi(B)`;
2. **uniform gap:** there are a finite symmetric `F subset L` and `kappa>0`
   with `max_(f in F) ||pi(sigma~(f))xi-xi|| >= kappa||xi||` for every
   `xi in Fix(L)^perp`;
3. there is a finite symmetric `F subset L` with `Fix(F)=Fix(L)` and
   `sp(h_F) subset [-1,1-c] union {1}` for some `c>0`;
4. `P_L in pi(C*(sigma~(<F>)))` for some finite `F subset L`; indeed
   `P_L=pi(chi_{1}(h_F))`.

**Consequences.**
- *No non-group source.* A transport projection for `L` taken from any element of `B`
  (carrier projections, corona modules, rank-germ projections, limits
  of anything) exists exactly when a finite Markov element of `L` has an
  isolated eigenvalue at `1`. So the escape "place `P_N` in `B` from outside
  every `A_K`" left by `root-column-fixed-projection-is-not-in-root-pair-cstar`
  is empty: `P_N in B` implies `P_N in A_N subset A_K`.
- *Infinite generation buys nothing.* Transport through `L` is transport
  through the finitely generated `<F>`, which has the same fixed vectors.
- *Locally finite `L`.* Then `<F>` is finite. So `P_L in B` iff
  `Fix(L)=Fix(L_0)` for one finite subgroup `L_0<=L`, and then `P_L` is the
  finite average over `L_0`.

Proof route: `corona-fixed-projection-membership-is-finite-markov-gap-proof`.
