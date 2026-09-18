---
rg: 2
id: universal-cover-lattice-hypertraces-kill-z-squared-proof
kind: route
title: The centralizer of an invariant state is a C-star algebra, so the state is an amenable trace; Kirchberg--Brown rigidity makes it a limit of finite-dimensional traces, where Deligne kills z squared
target: universal-cover-lattice-hypertraces-kill-z-squared
requires:
  - stw10-kazhdan-full-group-traces-are-qd
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
---

Notation of the target.  Write `B = C*(W(Gamma~)) <= B(H)` and
`pi_W : C*(Gamma~) -> B` for the integrated form (full group C-star
algebra, so `pi_W` is onto).

**Definition used (verbatim source).**  N. P. Brown, *Kazhdan's property T
and C\*-algebras*, arXiv:math/0602312v2 (24 Apr 2006), p. 4, fetched and
read 2026-09-18: "Definition 4.1. Let A ⊂ B(H) be a concretely represented
unital C\*-algebra. A tracial state τ on A is called amenable if there
exists a state ϕ on B(H) such that (1) ϕ|A = τ and (2) ϕ(uTu\*) = ϕ(T) for
every unitary u ∈ A and T ∈ B(H)."  Same page: "It is a remarkable fact
(due to Connes and Kirchberg) that this notion can be recast in terms of
approximation by finite dimensional completely positive maps", and in
particular it does not depend on the faithful representation chosen (this
is the ucp characterization, Brown's Theorem 4.2 there, whose statement
involves no representation).

## Step 1. `Phi|_B` is a tracial state and `Phi` is a hypertrace for it

Let

```text
Z_Phi = { a in B(H) : Phi(aT) = Phi(Ta) for all T in B(H) }.
```

It is a linear subspace, norm closed (`Phi` is bounded), closed under
products (`Phi(abT) = Phi(bTa) = Phi(Tab)`) and under adjoints
(`Phi(a^*T) = conj Phi(T^*a) = conj Phi(aT^*) = Phi(Ta^*)`, using
`Phi(x^*) = conj Phi(x)`).  So `Z_Phi` is a C-star subalgebra of `B(H)`.

By `(HT1)`, `Phi(W_g T) = Phi(W_g (T W_g) W_g^*) = Phi(T W_g)`, so every
`W_g` lies in `Z_Phi`; hence `B <= Z_Phi`.  Consequently `Phi(ab) = Phi(ba)`
for `a, b in B`, so `tau_B := Phi|_B` is a tracial state, and for every
unitary `u in B` and `T in B(H)`,
`Phi(u T u^*) = Phi(T u^* u) = Phi(T)`.  Thus `Phi` witnesses Brown's
Definition 4.1 for `tau_B` in the concrete representation `B <= B(H)`.

## Step 2. The pulled-back trace on `C*(Gamma~)` is amenable

Let `tau = tau_B o pi_W`, a tracial state on `C*(Gamma~)`.  Choose any
faithful representation `C*(Gamma~) <= B(K)` and represent `C*(Gamma~)`
faithfully on `H (+) K` by `x -> pi_W(x) (+) x`.  Put
`Phi'(T) = Phi(P_H T P_H)` for `T in B(H (+) K)`.  Every unitary of
`C*(Gamma~)` acts as `pi_W(u) (+) u`, which commutes with `P_H`, so
`P_H (pi_W(u)(+)u) T (pi_W(u)(+)u)^* P_H = pi_W(u) (P_H T P_H) pi_W(u)^*`,
and Step 1 (with `pi_W(u)` a unitary of `B`) gives
`Phi'(u T u^*) = Phi'(T)`.  Also `Phi'|_{C*(Gamma~)} = tau`.  So `tau` is
an amenable trace on `C*(Gamma~)` in the sense of Definition 4.1.

## Step 3. Kirchberg--Brown rigidity

`Gamma~` is a countable Kazhdan group
(`deligne-universal-cover-lattice-is-non-rf-kazhdan`, item 3; countable
because it is a central extension of the finitely generated `Sp_4(Z)` by
`Z`).  By `stw10-kazhdan-full-group-traces-are-qd` (Brown's memoir,
Proposition 4.1.12), `tau` is a pointwise limit

```text
tau(x) = lim_k tr_{d_k}(sigma_k(x)),      x in C*(Gamma~),
```

of normalized traces of finite-dimensional unitary representations
`sigma_k : Gamma~ -> U(d_k)`.

## Step 4. Finite-dimensional representations of `Gamma~` kill `z^2`

Let `sigma : Gamma~ -> U(d)`.  Its image is a finitely generated linear
group, hence residually finite (Mal'cev's theorem).  Let
`f : Gamma~ -> F` be any homomorphism onto a finite group and let `m` be
the order of `f(z)`.  If `m <= 2` then `f(z^2) = 1`.  If `m >= 3`, `f`
factors through `Gamma~/<z^m>`, which is the preimage `Gamma_m` of
`Sp_4(Z)` in the connected `m`-fold cover of `Sp_4(R)`, with `z` mapping
to the covering generator.  By `deligne-covers-of-sp2g-z-have-finite-residual-2z`
(Deligne; `g = 2`, `m >= 3`) every finite quotient of `Gamma_m` kills the
image of `2Z`, so again `f(z^2) = 1`.  Thus `z^2` lies in every
finite-index normal subgroup of `Gamma~`, and its image `sigma(z^2)` lies
in every finite-index normal subgroup of the residually finite group
`sigma(Gamma~)` (their preimages have finite index in `Gamma~`).  Hence
`sigma(z^2) = I`.

## Step 5. Conclusion

By Steps 3 and 4, `tau(z^2) = lim_k tr_{d_k}(I) = 1`, i.e.
`Phi(W_z^2) = 1`.  Since `W_z^2` is unitary and `Phi` is a state,
`Phi((1 - W_z^2)^*(1 - W_z^2)) = 2 - 2 Re Phi(W_z^2) = 0`, and the
Cauchy--Schwarz inequality gives `Phi(T(1 - W_z^2)) = 0` for all `T`.
Finally each `sigma_k(z)` is a self-adjoint unitary (`sigma_k(z)^2 = I`),
so `tr(sigma_k(z)) in [-1,1]` and `Phi(W_z) = tau(z) in [-1,1]`.  This is
`(HT2)`.

**What was not used.**  No descent of amenability to a quotient: the trace
is only ever pulled back (Step 2), which is always legitimate.  No
assumption on `W_z` (it need not be scalar), and no assumption that `B`
lacks finite-dimensional quotients.  This is what distinguishes the
statement from `odd-maslov-twisted-fibres-have-no-amenable-trace`, which
it contains as the special case `W_z = lambda I`, `lambda^2 != 1`
(a trace on `A_theta` extended to a hypertrace would give `Phi(W_z^2) =
lambda^2 != 1`) for the three-fold and six-fold parameters, and extends to
every `theta notin (1/2)Z/Z`.
