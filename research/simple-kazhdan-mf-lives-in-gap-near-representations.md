---
rg: 2
id: simple-kazhdan-mf-lives-in-gap-near-representations
kind: claim
title: Operator-norm local rigidity is free for rationally perfect groups, so MF-ness of a finitely presented simple Kazhdan group lives entirely in spectral-gap near-representations
distinct_from:
  padding-makes-local-hs-rigidity-global: in normalized Hilbert--Schmidt norm, padding by identity blocks turns local linear rigidity near the trivial tuple into the global inequality; in operator norm padding does nothing (the norm of a direct sum is a maximum), local linear rigidity holds for free by rational perfectness, and this claim shows the whole MF question sits at a definite distance from the trivial tuple.
  abelian-extensions-kill-kcf-compression-defects: that kills group-theoretic compression-defect mechanisms on K x Z; this is a representation-level reformulation of the remaining clause "K not MF" and kills the perturbative class.
  irreducible-kazhdan-representations-have-uniform-hs-rigidity: that is Hilbert--Schmidt rigidity around genuine irreducible representations; here the only genuine finite-dimensional representation is trivial and the statement is in operator norm.
  kazhdan-almost-invariant-corner-near-invariant-projection: that corrects an almost-invariant projection under a genuine representation; this lifts the Kazhdan projection through an asymptotic homomorphism into the norm corona.
---

**ESTABLISHED** (route `simple-kazhdan-mf-lives-in-gap-near-representations-proof`).

Let `K = <S | R>` be finitely presented. For a tuple `u` in `U(k)^S`, with operator norms, put

```text
D(u) = max_s ||u_s - 1||,    d(u) = max_r ||r(u) - 1||,    Delta(u) = sum_s (2 - u_s - u_s^*).
```

**(A) Local linear rigidity (every finitely presented `K` with `H_1(K;Q) = 0`).** There are
`eps_0, C > 0`, depending only on the presentation and computable from it, such that every tuple
in every dimension with `D(u) <= eps_0` satisfies `D(u) <= C d(u)`.

**(B) Gap reformulation.** Assume in addition that `K` is infinite, simple and Kazhdan. Let `kappa > 0`
be the spectral gap of `Delta` in `C*(K)`, so its spectrum lies in `{0} ∪ [kappa, 4|S|]`. For
`0 < t` and `k >= 1` put

```text
delta_t(k) = min { d(u) : u in U(k)^S, Delta(u) >= t·1 }.
```

Then each `delta_t(k)` is attained and positive. For every `t` in `(0, kappa)`:

```text
K is not MF   <=>   inf_k delta_t(k) > 0
              <=>   there are delta_0, C' > 0 with D(u) <= C' d(u) for all tuples with d(u) <= delta_0.   (GAP)
```

**(C) Arithmetic form.** For rational `t` and `q`, "`delta_t(k) < q`" is decidable, uniformly in `k`
(Tarski--Seidenberg). Fix any rational `t_0` in `(0, kappa)`. Then "`K` is MF" is the `Pi_2` sentence
`forall m exists k : delta_(t_0)(k) < 1/m`, and "`K` is not MF" is `Sigma_2`. This claim does not assert that such a
`t_0` can be computed. That would come from an exact rational Ozawa sum-of-squares certificate
`Delta^2 - eps Delta in Sigma^2 R[K]` together with the solvable word problem, and it is recorded as a remark only.

**Consequence for `titz-witzel-exact-kazhdan-mf-radical-over-z`.** For a Titz Mite--Witzel residual `K`,
the open clause "`K` not MF" is exactly (GAP). Every tuple with `Delta(u) >= t` has `D(u) >= sqrt(t/|S|)`,
and the only genuine finite-dimensional representation of `K` is trivial. So the class of *perturbative*
arguments dies, and this includes:

- linearization at genuine representations;
- cohomology with coefficients in their adjoint modules;
- defect-diminishing started in a neighbourhood of a genuine representation;
- the Hilbert--Schmidt padding trick.

Such an argument sees only (A), which is automatic. It is also true for groups that are MF: `SL_3(Z)` is
finitely presented, perfect and residually finite. A proof of the target must exclude near-representations
at operator distance at least `sqrt(t/|S|)` from every genuine representation.
