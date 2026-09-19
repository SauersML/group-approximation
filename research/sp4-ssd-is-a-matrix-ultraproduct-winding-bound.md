---
rg: 2
id: sp4-ssd-is-a-matrix-ultraproduct-winding-bound
kind: claim
title: The single-scale winding deficit is exactly a trace-winding bound for uniform quasi-representations of Sp4(Z) into one matrix ultraproduct, and rounding to homomorphisms there proves it
distinct_from:
  sp4-winding-ratio-is-an-infimum-over-scales: that proves superadditivity in the defect and reduces the deficit hole to one scale; this rewrites that one-scale inequality, with no loss, as a statement about maps into the single C*-algebra Q, and gives a stability criterion for it.
  sp4-quasirep-single-scale-winding-deficit: that is the open inequality (SSD); this proves an exact reformulation of it and a sufficient condition, and decides nothing.
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that computes the ceiling of the winding ratio from bounded cohomology; this is about which algebra the witnesses may be taken in.
  mf-radical-is-blind-to-degree-two-windings: that kills winding certificates for MF-radical membership; this uses the trace-winding only as an obstruction to rounding plain Sp_4(Z) quasi-representations, where it is the whole of (SSD).
---

**ESTABLISHED** (route `sp4-ssd-is-a-matrix-ultraproduct-winding-bound-proof`). Unreviewed.

**Setting.** The notation is that of `sp4-quasirep-windings-budget-and-saturation` and
`sp4-winding-ratio-is-an-infimum-over-scales`:
- `Gamma = Sp_4(Z)`, and a relator `r = prod_{i<=g} [a_i, b_i]` with lifted value `zeta^k`, `k != 0`;
- `W_r(pi) = prod [pi(a_i), pi(b_i)]`, finite windows `W` containing `W_r`, and `S_W(eps)` on `(0, a_g]`;
- `a_g = 1/(6g-1)`, `tau_W = |k|/(2 pi beta*_W)`, and `nu = ||[r]||_1 > 0`.

Put `S_W(eps+) = inf_{eps < eps' <= a_g} S_W(eps')` for `eps in (0, a_g)`.

**The algebra.** Fix a free ultrafilter `omega` on `N`, and put
`Q = prod_n M_(n!) / c_omega`, where `c_omega` is the set of sequences with `||x_n|| -> 0` along `omega`.
`Q` carries the tracial state `tau([x_n]) = lim_omega tr_(n!)(x_n)`, where `tr` is the normalized trace.

For a unital C*-algebra `A` with tracial state `tau_A`, and a unital `Pi : Gamma -> U(A)` with
`||W_r(Pi) - 1|| < 2`, the **trace-winding** is `kappa^tau(Pi) = (1/(2 pi i)) tau_A(log W_r(Pi))`, principal
branch. It is real. For `A = M_d` it is `kappa_r(pi)/d`. Set

```text
w_W(eps) = sup { |kappa^tau(Pi)| : Pi : Gamma -> U(Q) unital, ||Pi(g)Pi(h) - Pi(gh)|| <= eps on W },
w(eps)   = sup { |kappa^tau(Pi)| : Pi : Gamma -> U(Q) unital, ||Pi(g)Pi(h) - Pi(gh)|| <= eps for ALL g, h }.
```

Call the maps in the second supremum *uniform `eps`-quasi-representations into `U(Q)`*.

**Theorem.** Let `eps in (0, a_g)`.
1. **Ultraproduct identity, attained.** `w_W(eps) = S_W(eps+)` and `w(eps) = inf_W S_W(eps+)`. Both suprema are
   maxima. In particular, one map `Pi : Gamma -> U(Q)`, with defect `<= eps` on every pair of `Gamma`, reaches
   `kappa^tau(Pi) = inf_W S_W(eps+)`.
2. **(SSD) is a statement about `Q`.** The window-free form of (SSD) in `sp4-quasirep-single-scale-winding-deficit`
   asks for one `(W, eps_1)` with `S_W(eps_1) < eps_1 nu/(2 pi)`. It holds iff there is `eps_0 in (0, a_g)` such that
   every uniform `eps_0`-quasi-representation `Pi : Gamma -> U(Q)` has

   ```text
   |kappa^tau(Pi)|  <  eps_0 nu / (2 pi).                                    (SSD_Q)
   ```

   Similarly, (SSD) itself, with `tau_W`, holds iff some `W` and some `eps_0 in (0, a_g)` have `w_W(eps_0) < tau_W eps_0`.
   Contrapositive: (SSD) in window-free form fails iff for every `eps in (0, a_g)` there is one uniform
   `eps`-quasi-representation `Pi_eps : Gamma -> U(Q)` with `kappa^tau(Pi_eps) >= eps nu/(2 pi)`.
3. **Homotopy invariance.** Let `(A, tau_A)` be a unital C*-algebra with a tracial state. Let `x_1, ..., x_(2g)` be
   `C^1` paths `[0,1] -> U(A)` with `||prod_i [x_(2i-1)(s), x_(2i)(s)] - 1|| < 2` for all `s`. Then
   `tau_A(log prod_i [x_(2i-1)(s), x_(2i)(s)])` does not depend on `s`.
4. **Rounding criterion.** Let `Pi : Gamma -> U(Q)` have defect `<= eps` on `W_r`. Let `theta : Q -> M` be a unital
   *-homomorphism into a unital C*-algebra with a tracial state `tau_M` such that `tau_M o theta = tau`. Suppose some
   unitaries `v_y in U(M)`, `y in {a_i, b_i}`, satisfy

   ```text
   prod_i [v_(a_i), v_(b_i)] = 1,    ||v_y - theta(Pi(y))|| <= delta,    (6g-1) eps + 4 g delta < 2.
   ```

   Then `kappa^tau(Pi) = 0`. This holds in particular if `delta < 1/(4g)` and `theta o Pi` is `delta`-close on the
   `2g` letters to a homomorphism `Rho : Gamma -> U(M)`.
5. **Stability implies the deficit.** Suppose that for one `eps_0 in (0, a_g)`, every uniform `eps_0`-quasi-representation
   into `U(Q)` satisfies the hypothesis of item 4. Then `w(eps_0) = 0`. Hence (SSD) holds with `c` as small as wanted:
   for every `c > 0` some `W` and `eps_1 in (eps_0, a_g]` have `S_W(eps_1) < c eps_1`. So `Theta_inf = 0`, and
   `sp4-quasirep-winding-ratio-has-a-deficit` follows.
6. **The all-MF branch blocks every rounding.** If `P_op = R/Z`, then `w(eps) >= nu eps/(2 pi) > 0` for every
   `eps in (0, a_g)`. So at every scale there is a uniform `eps`-quasi-representation into `U(Q)` that is not
   `delta`-close on the letters, for any `delta < (2 - (6g-1) eps)/(4g)`, to any exact solution of
   `prod [x_i, y_i] = 1` in any trace-preserving image of `Q`.

**What this changes.**
- (SSD) was a supremum over all dimensions and all windows. It is now one bound on one fixed algebra `Q`, and the
  bound is attained. A counterexample to (SSD) is a single uniform quasi-representation per scale, not a sequence.
- The target algebra is forced. A w17 lemma posted live but not yet in this graph (sp4-winding-deficit-fails-in-twisted-tracial-algebras,
  by swarm-0917-w17-w17-deligne-last1) shows the same bound is false in the twisted tracial algebras
  `C*_lambda(Gamma, e(tb))`. Item 1 shows it holds or fails with `Q` in their place, with no loss. So the matricial
  content of (SSD) is exactly the question of which uniform quasi-representations into `U(Q)` exist. When `t in P_op`, the
  parameter models of `deligne-sep7-norm-parameter-closed-subgroup` put such witnesses on every window into `Q`, and
  that is item 6.
- Item 4 turns (SSD) into a rounding problem at one fixed scale in operator norm, uniform in the dimension. That is
  the uniform-stability setting of Glebsky–Lubotzky–Monod–Rangarajan. There it is proved for many higher-rank
  lattices and is explicitly not available for type `C_n` (quoted in `sp4-ultraproduct-quasireps-round-to-homs-at-one-scale`).
  The open prerequisite is recorded there, and the route is `sp4-single-scale-deficit-from-ultraproduct-rounding`.

**Remarks on scope.**
- *Rounding only needs the surface relation, but that form is not a new condition.* Item 4 uses only
  `prod [v_(a_i), v_(b_i)] = 1`. The target `M` may be the tracial ultraproduct `prod^omega (M_(n!), tr)`, which
  cannot see corners of relative rank `o(1)`. There a winding `k_n = o(n!)` can plausibly be cancelled by a direct
  summand of small relative size. If so, rounding to exact surface-group solutions would be equivalent to
  `kappa^tau(Pi) = 0`, so it adds nothing to (SSD_Q). This is not proved here. It is why the open prerequisite asks
  for homomorphisms of `Gamma` itself.
- *Finite-dimensional uniform stability does not give item 5's hypothesis directly.* A uniform
  `eps_0`-quasi-representation into `U(Q)` lifts, by item 1's proof, only to maps `pi_n : Gamma -> U(n!)` whose defect
  is small on finite windows that grow with `n`. It need not be small on all of `Gamma x Gamma` for any `n`. So a
  dimension-uniform theorem in the sense of GLMR for `Sp_4(Z)`, stated for maps into `U(d)` with defect small on all
  of `Gamma`, would have to be run inside `Q` (GLMR's own framework is ultraproducts of such maps), not quoted.
- *Pointwise operator-norm non-stability is no obstruction.* Dadarlat's nonzero windings
  (`dadarlat-linear-groups-have-nonzero-h2-windings`) have normalized winding tending to `0`. In `Q` their
  asymptotic representations are exact homomorphisms `Gamma -> U(Q)` with `kappa^tau = 0`, and item 4 accepts them.
