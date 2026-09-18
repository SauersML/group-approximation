---
rg: 2
id: exact-x1-reduces-to-q-stable-algebras-proof
kind: route
title: Pull quasidiagonal models back along a tensor with 1 and push them forward by tensoring models
target: exact-x1-reduces-to-q-stable-algebras
requires: [tww-gabe-schafhauser-af-embedding-theorem]
---

**Conventions.** A tracial state `tau` on a unital C\*-algebra `A` is
*quasidiagonal* if there are u.c.p. maps `phi_n : A -> M_{k_n}` with

- `||phi_n(ab) - phi_n(a) phi_n(b)|| -> 0` for all `a, b`;
- `tr_{k_n} ∘ phi_n -> tau` pointwise.

Equivalently, write `M_∞ = ∏_n M_{k_n} / ⊕_n M_{k_n}` with the limit trace
along a free ultrafilter. Then `tau` is quasidiagonal iff it arises from a
unital `*`-homomorphism `A -> M_∞` that has a u.c.p. lift. The same argument
works with sequences replaced by nets, for non-separable `A`.

**Step 1 (Theorem 1(1): pullback).** The map `iota : A -> A ⊗_min C`,
`a ↦ a ⊗ 1`, is a unital `*`-homomorphism with `(tau ⊗ sigma) ∘ iota = tau`.
If the maps `psi_n` are quasidiagonal models for `tau ⊗ sigma`, then
`psi_n ∘ iota` are u.c.p., and

```text
||psi_n(iota(ab)) - psi_n(iota a) psi_n(iota b)|| = ||psi_n(iota(a) iota(b)) - psi_n(iota a) psi_n(iota b)|| -> 0,
```

while `tr ∘ psi_n ∘ iota -> tau`. So `tau` is quasidiagonal.

**Step 2 (Theorem 1(2): tensoring models).** Let `phi_n : A -> M_{k_n}` and
`chi_n : C -> M_{l_n}` be quasidiagonal models. Their tensor product
`Phi_n = phi_n ⊗ chi_n : A ⊗_min C -> M_{k_n} ⊗ M_{l_n}` is u.c.p., since the
spatial tensor product of u.c.p. maps is u.c.p.

*Multiplicativity.* Form the induced u.c.p. map
`Phi : A ⊗_min C -> ∏ M_{k_n l_n} / ⊕ M_{k_n l_n}`. For elementary tensors,

```text
Phi_n((a⊗c)(a'⊗c')) - Phi_n(a⊗c) Phi_n(a'⊗c')
   = (phi_n(aa') - phi_n(a)phi_n(a')) ⊗ chi_n(cc')  +  phi_n(a)phi_n(a') ⊗ (chi_n(cc') - chi_n(c)chi_n(c')),
```

whose norm is at most
`||phi_n(aa')-phi_n(a)phi_n(a')|| ||c|| ||c'|| + ||a|| ||a'|| ||chi_n(cc')-chi_n(c)chi_n(c')||`,
which tends to `0`. So `Phi` is multiplicative on elementary tensors, and in
particular `Phi(x^*x) = Phi(x)^*Phi(x)` and `Phi(xx^*) = Phi(x)Phi(x)^*` for
each elementary tensor `x`.

The multiplicative domain of a u.c.p. map is a C\*-subalgebra (Choi). It
contains the elementary tensors, which generate `A ⊗_min C`, so `Phi` is a
`*`-homomorphism. That is exactly asymptotic multiplicativity of `Phi_n` in
operator norm.

*Trace.* `tr(Phi_n(a ⊗ c)) = tr(phi_n(a)) tr(chi_n(c)) -> tau(a) sigma(c)`.
The maps are contractive, so this extends from the algebraic tensor product to
`tr ∘ Phi_n -> tau ⊗ sigma` pointwise on `A ⊗_min C`.

**Step 3 (Theorem 1(3)).** `tau_Q` is quasidiagonal: `Q` is an inductive
limit of matrix algebras, and conditional expectations onto the finite stages
give models. Apply Steps 1 and 2 with `C = Q`.

**Step 4 (Theorem 2).** (a) ⇒ (b) is trivial.

For (b) ⇒ (a), let `tau` be an amenable trace on an exact `A` that is not
quasidiagonal. By the reductions recorded in
`amenable-traces-on-exact-cstar-algebras-are-quasidiagonal` (separable unital
subalgebra, then the GNS quotient), we may assume `A` is separable, unital
and exact and `tau` is faithful and amenable. Put `B = A ⊗ Q`. Then:

- **`B` is separable, unital, exact and `Q`-stable.** It is exact because
  spatial tensor products of exact algebras are exact, and `Q`-stable because
  `Q ⊗ Q ≅ Q`.
- **`tau ⊗ tau_Q` is faithful.** A tracial state whose GNS representation is
  faithful is faithful. Indeed, if `rho(x^*x) = 0`, then for all `y`,
  `||pi(x) pi(y) xi||^2 = rho(y^* x^* x y) = rho(x y y^* x^*) <= ||y||^2 rho(x x^*) = ||y||^2 rho(x^* x) = 0`,
  so `pi(x) = 0`. The GNS representation of `tau ⊗ tau_Q` is `pi_tau ⊗ pi_{tau_Q}`,
  which is faithful on the spatial tensor product because both factors are
  faithful.
- **`tau ⊗ tau_Q` is amenable.** Its GNS closure is `pi_tau(A)'' ⊗̄ R`, which
  is injective. `B` is exact, so the injective-GNS characterisation of
  amenability applies (Brown, Corollary 4.3.4).

By (b), `tau ⊗ tau_Q` is quasidiagonal, so by Step 1 `tau` is quasidiagonal,
a contradiction.

*Remarks on (b).*

- **Uniquely divisible K-theory.** `K_*(B) = K_*(A) ⊗ Q` by continuity of
  K-theory along `A ⊗ M_{n!}`.
- **`Z`-stable.** `Q ≅ Q ⊗ Z`.
- **Every trace is `rho ⊗ tau_Q`.** Let `T` be a trace on `B` and `a ≥ 0` in
  `A`. The functional `c ↦ T(a ⊗ c)` is positive, and it is tracial because
  `T(a⊗cd) = T((a^{1/2}⊗c)(a^{1/2}⊗d)) = T((a^{1/2}⊗d)(a^{1/2}⊗c)) = T(a⊗dc)`.
  So it equals `T(a⊗1) tau_Q(c)` by uniqueness of the trace on `Q`, and
  linearity and density give `T = rho ⊗ tau_Q` with `rho = T(· ⊗ 1)`.

**Step 5 (Corollary 3).** Let `A` be separable exact with faithful amenable
`tau`, and let `C` be separable exact with faithful amenable `sigma` such that
`A ⊗ C` satisfies the UCT. As in Step 4:

- `A ⊗ C` is separable and exact;
- `tau ⊗ sigma` is faithful;
- its GNS closure `pi_tau(A)'' ⊗̄ pi_sigma(C)''` is injective, so it is
  amenable.

By `tww-gabe-schafhauser-af-embedding-theorem` in Schafhauser's
trace-extending form, `A ⊗ C` embeds in a simple AF algebra `D` with a trace
`tau_D` extending `tau ⊗ sigma`. Every trace on an AF algebra is
quasidiagonal: compress by conditional expectations onto finite-dimensional
subalgebras whose union is dense. Quasidiagonality passes to restrictions
along `*`-homomorphisms, as in Step 1. So `tau ⊗ sigma` is quasidiagonal, and
by Step 1 so is `tau`.

For `C = M_{P^∞}` the hypothesis says `P ∈ 𝒫(A)`, so it holds whenever the
filter `𝒫(A)` is nonempty. The filter is upward closed and `M_{P^∞} ⊗ Q ≅ Q`,
so it is nonempty iff `A ⊗ Q` satisfies the UCT.

**Step 6 (Corollary 4).** The first item is the contrapositive of Corollary 3.
For the second, Step 4 shows `tau ⊗ tau_Q` is faithful and amenable on the
separable exact algebra `A ⊗ Q`, and Step 1 shows it is not quasidiagonal.

**Where exactness enters.** Only in two places:

1. the amenable ⇔ injective-GNS characterisation;
2. the input theorem.

Steps 1--3 hold for all C\*-algebras. So nothing here yields a
quasidiagonality claim for the non-exact counterexample `C*(E)`.
