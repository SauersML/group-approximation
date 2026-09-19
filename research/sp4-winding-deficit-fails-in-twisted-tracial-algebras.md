---
rg: 2
id: sp4-winding-deficit-fails-in-twisted-tracial-algebras
kind: claim
title: Exact twisted regular unitaries of Sp4(Z) beat the all-MF winding ratio at every scale in a tracial algebra, so no dimension-free argument can prove the single-scale winding deficit
distinct_from:
  sp4-winding-ratio-sharp-constant-is-gromov-dual: item 8 there kills arguments that keep finite dimension and integrality but forget the traceless part of the defects; this kills arguments that keep the full operator data but forget finite dimension, and its witnesses have zero traceless defect.
  sp4-quasirep-single-scale-winding-deficit: that is the open matricial inequality (SSD); this proves that the same inequality is false at every window and every scale once matrix algebras are replaced by tracial C*-algebras, and so names what any proof of (SSD) must use.
  deligne-fixed-projective-representation-folner-compression-no-go: that shows a fixed exact Maslov representation has no finite-rank Folner compressions; this uses the exact twisted regular representation at every real parameter as a tracial witness, and makes no claim about compressions.
  mf-radical-is-blind-to-degree-two-windings: that kills winding certificates for MF-radical membership through realification; this is about the winding-to-defect ratio of plain Sp_4(Z) quasi-representations and kills trace-valid upper bounds on it.
---

**ESTABLISHED** (route `sp4-winding-deficit-fails-in-twisted-tracial-algebras-proof`). Unreviewed.

**Setting.** The notation is that of `sp4-quasirep-windings-budget-and-saturation`,
`sp4-winding-ratio-sharp-constant-is-gromov-dual` and `sp4-winding-ratio-is-an-infimum-over-scales`:
- `Gamma = Sp_4(Z)`, `b` the normalized integral covering cocycle, `E_infinity = Gamma x_b Z`, `zeta = (e,1)`;
- a relator `r = prod_{i<=g} [a_i,b_i]` with `prod [a_i^, b_i^] = zeta^k`, `k != 0`;
- a finite window `W` containing `W_r`, `beta*_W = min_psi max_W |b + delta psi|`, `tau_W = |k|/(2 pi beta*_W)`,
  and `a_g = 1/(6g-1)`.

**Tracial winding.** Let `(A, tau)` be a unital C*-algebra with a tracial state. For a unital map
`pi : Gamma -> U(A)` with `||W_r(pi) - 1|| < 2`, put `kappa_r^tau(pi) = (1/(2 pi i)) tau(log W_r(pi))`, with the
principal branch. Put

```text
S_W^A(eps) = sup { |kappa_r^tau(pi)| : pi : Gamma -> U(A) unital, ||pi(g)pi(h) - pi(gh)|| <= eps on W }.
```

For `A = M_d` with the normalized trace, `kappa_r^tau(pi) = kappa_r(pi)/d`. So `S_W(eps) = sup_d S_W^(M_d)(eps)`, and
(SSD) of `sp4-quasirep-single-scale-winding-deficit` asks for `S_W^(M_d)(eps_1) <= c eps_1` for all `d`, with `c < tau_W`.

**Theorem.** For real `t`, let `A_t = C*_lambda(Gamma, e(tb))` be the twisted reduced group C*-algebra, with canonical
unitaries `u_g` satisfying `u_g u_h = e(t b(g,h)) u_(gh)` and canonical trace `tau(x) = <x delta_e, delta_e>`.
Fix a minimizer `psi*` for `beta*_W`, and put `pi_t(g) = e(t psi*(g)) u_g`.
1. **Exact data.** `pi_t` is unital, and on `W`
   ```text
   ||pi_t(g)pi_t(h) - pi_t(gh)|| = 2 |sin(pi t (b + delta psi*)(g,h))| <= 2 sin(pi |t| beta*_W)   when |t| beta*_W <= 1/2.
   ```
   Every defect `pi_t(g)pi_t(h)pi_t(gh)^*` is a scalar, so the traceless part of each defect is 0. Also
   `W_r(pi_t) = e(tk) 1`.
2. **Winding.** For `|t| beta*_W <= (1/pi) arcsin(a_g/2)`, the tracial winding is `kappa_r^(tau)(pi_t) = tk`.
3. **Saturation at every scale, strictly.** For every `eps in (0, a_g]`, let `t(eps) = arcsin(eps/2)/(pi beta*_W)`.
   Then `pi_(t(eps))` has defect `<= eps` on `W`, and

   ```text
   S_W^(A_t(eps))(eps) / eps  >=  |k| t(eps)/eps  =  tau_W * (2 arcsin(eps/2))/eps  >  tau_W.
   ```

   So the analogue of (SSD) fails in the tracial class, at every finite window, every scale `eps_1 in (0, a_g]` and
   every constant `c < tau_W`. It also fails for `c = tau_W`, and for the window-free constant `nu/(2 pi)`, which is
   at most `tau_W`.
4. **Rational windings too.** For every `eps in (0, a_g]` and every `c' < tau_W (2 arcsin(eps/2))/eps`, there is a
   rational `t` with `|tk| = j/d` for integers `j, d > 0`, defect `<= eps` on `W`, and `|kappa_r^tau(pi_t)| >= c' eps`.
   So the analogue of (SSD) also fails when the tracial winding is additionally required to lie in `(1/d)Z` for some
   integer `d`, which is the integrality that holds in `M_d`.
5. **Tracial non-stability.** Every unital map `rho : Gamma -> U(A_t)` that is multiplicative on `W_r` has
   `max_(y in {a_i, b_i}) ||rho(y) - pi_t(y)|| >= |e(tk) - 1|/(4g)`. So the witnesses are not near exact
   representations. No tracial perturbation argument at fixed scale can move them there.

**The class that dies.** Call an argument *dimension-free* if the bound it proves on `|kappa_r^tau(pi)|` holds for
unital `W`-maps into every unital C*-algebra with a tracial state, or even only into the algebras `A_t` with
`|t| beta*_W <= (1/pi) arcsin(a_g/2)`. Examples:
- Kazhdan-pair and spectral-gap estimates for the conjugation action on `L^2(A, tau)`;
- tracial sum-of-squares and moment certificates;
- Haagerup-type or Hilbert-module inequalities;
- perturbation-to-exact arguments in the tracial category.

No dimension-free argument proves (SSD), `sp4-quasirep-winding-ratio-has-a-deficit` or
`sp4-quasirep-windings-are-sublinear`. The last two are included because tracial superadditivity is not needed: by
item 3, the tracial ratio exceeds `tau_W` at every scale, and so its limsup does too.
- *Invariant.* The tracial winding `tau(log W_r)/(2 pi i)` of the exact twisted regular unitaries, which equals `tk`.
- *Step where every member dies.* The claimed inequality `|kappa_r^tau(pi)| <= c eps`, which `pi_(t(eps))` violates
  in `A_(t(eps))`.
Item 4 shows the argument can additionally use rationality of the winding and still die.

**What a proof of (SSD) must use.** Item 8 of `sp4-winding-ratio-sharp-constant-is-gromov-dual` kills the *scalar
hull*: finite dimension and integral determinant windings, with the traceless part forgotten. This node kills the
*tracial hull*: all operator data, with finite dimension forgotten. Its witnesses have zero traceless defect on all of
`Gamma x Gamma`. In `M_d` that cannot happen for small `t != 0`. A map with scalar defects everywhere is an exact
projective representation, and `sp4-fd-projective-multiplier-is-finite` says only finitely many classes in
`H^2(Gamma, T)` arise this way. A coboundary evaluates to `1` on the integral cycle `c_r`, and `e(tb)` evaluates
to `e(tk)` there. So the classes of `e(tb)` for `0 <= t < 1/|k|` are pairwise distinct, and all but finitely many of
them have no exact finite-dimensional realization. So:

```text
a proof of (SSD) must bound the traceless part of the defects from below in terms of the winding,
using a property of M_d that fails in A_t for small t != 0.
```

Such properties include finite-rank compression (as in `deligne-fixed-projective-representation-folner-compression-no-go`),
matricial stability, and residual finiteness input. Operator-norm stability of `Gamma` into tracial C*-algebras is not
among them, by item 5.

**Consistency.** At `t = 1/3` the same construction is the exact `omega`-projective regular representation of the
twisted fibre. So the tracial parameter group is all of `R/Z`, which matches the central-regular traces recorded for
the twisted fibres. Nothing here decides (SSD) or `P_op`.
