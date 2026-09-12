# Formalizability of a binary left-inverse pair is a Boolean-ideal cokernel class

Lane `gk-fz-obstruction`, 2026-09-12. Supports
`formalizability-is-a-boolean-ideal-cokernel-class` and
`formalizability-conormal-obstruction-is-jacobian-cokernel`, and bears on the open
target `binary-left-inverse-pairs-are-formalizable` and its consumer
`stable-finiteness-forces-binary-surjunctivity`.

This lane sets up formalizability, in the sense of
`binary-left-inverse-pairs-are-formalizable`, as the vanishing of an obstruction
class, reduces the infinite nonlinear search for representatives to one linear
equation over the Boolean ideal, and identifies the leading part of that class
with a Jacobian cokernel over `F_2[G]` — the same object `Theorem 1` of
`formal-polynomial-strict-pairs-2026-09-12.md` linearizes to. Nothing here
decides formalizability or Gottschalk.

## 1. Coordinate-algebra setting

Work over `k = F_2`, alphabet `A = F_2^n`. Let `H = G x {1,...,n}` index the
coordinates, `R = F_2[X_h : h in H]` the polynomial ring, `I = (X_h^2 + X_h : h)`
the Boolean ideal, and `B = R/I`. `B` is the algebra of finite-memory functions
`A^G -> F_2`: it is `colim_F Fun(A^F, F_2)`, a commutative Boolean ring, and it
carries the shift action of `G`.

A cellular map `tau : A^G -> A^G` of finite memory pulls back to a `G`-equivariant
`F_2`-algebra endomorphism `tau^* : B -> B` of finite memory. `tau` is injective
iff `tau^*` is surjective; `tau` is surjective iff `tau^*` is injective.

**Representatives are lifts.** A polynomial representative of `tau`'s local rule is
a choice, for each `i`, of `hat mu_i in F_2[X_m : m in M]` (finite memory `M`)
reducing to `tau(x)_{1,i}` in `B`. Extended equivariantly, `X_{g,i} -> g . hat mu_i`,
this is a `G`-equivariant `F_2`-algebra map `hat tau^* : R -> R` lifting `tau^*`
along `R -> R/I = B`. Conversely every such lift is a representative.

**Every lift preserves `I`.** For any lift, `hat tau^*(X_h^2 + X_h) = hat mu_h^2 +
hat mu_h`, whose image in `B` is `y^2 + y` for `y = tau^*(bar X_h)`. `B` is Boolean,
so `y^2 = y` and the image is `0`. Hence `hat tau^*(I) subseteq I`. No hypothesis on
`tau` is used.

**Formalizability.** As functions `(sigma o tau)^* = tau^* sigma^*`, so
`sigma o tau = id` means `tau^* sigma^* = id_B`, i.e. `hat tau^* hat sigma^* = id`
modulo `I` on generators. The pair is *formalizable* when some lifts satisfy
`hat tau^* hat sigma^* = id_R` exactly. Coordinatewise this is the artifact
convention "`sigma o tau = id` as a formal polynomial identity", since the
substituted polynomial for coordinate `(g,i)` is `hat tau^* hat sigma^*(X_{g,i})`.

## 2. The exact linear reformulation

Fix a lift `hat tau^*` of `tau^*` and any lift `hat sigma_0^*` of `sigma^*`. Both
lift `tau^*, sigma^*` with `tau^* sigma^* = id_B`, so on each generator

```text
hat tau^* hat sigma_0^*(X_h) = X_h + eps_h,   eps_h in I.
```

Replace `hat sigma_0^*` by the lift `hat sigma^*` with
`hat sigma^*(X_h) = hat sigma_0^*(X_h) + delta_h`, `delta_h in I` (finite memory,
equivariant). This is again an algebra map lifting `sigma^*`, because an assignment
of generators extends uniquely to an algebra map and `delta_h in I` does not change
the reduction mod `I`. Since `hat tau^*` is an algebra map, hence additive,

```text
hat tau^* hat sigma^*(X_h) = hat tau^* hat sigma_0^*(X_h) + hat tau^*(delta_h)
                           = X_h + eps_h + hat tau^*(delta_h).
```

There are **no higher-order corrections**: `hat sigma^*` is determined by its values
on generators, so agreement on generators is agreement as algebra maps. Therefore

> **Proposition 1.** With `hat tau^*` fixed, the pair is formalizable iff the linear
> equations `hat tau^*(delta_h) = eps_h` are solvable with `delta_h in I`. Since
> `hat tau^*(I) subseteq I` and `eps_h in I`, this is vanishing of the class
> `[eps] = ([eps_h])_h` in `coker(hat tau^*|_I)`, one coordinate per `i` after
> quotienting by equivariance.

Equivariance reduces the `H`-indexed system to `n` equations
`hat tau^*(delta_i) = eps_i` (`i = 1,...,n`) in the finite-memory part of `I`:
applying `g` to a solution of the `i`-th equation gives the `(g,i)` equation, since
`hat tau^*` and `eps` are equivariant.

**Representative independence (`sigma` side).** Changing `hat sigma_0^*` within its
function class replaces `hat sigma_0^*(X_h)` by `hat sigma_0^*(X_h) + delta'_h`,
`delta'_h in I`, hence `eps_h` by `eps_h + hat tau^*(delta'_h)`. That lies in the
same coset of `hat tau^*(I)`. So `[eps] in coker(hat tau^*|_I)` depends only on the
functions `tau, sigma`, once `hat tau^*` is fixed. Formalizability is
`[eps] = 0` for some choice of `tau`-lift `hat tau^*`.

**Sitewise pairs vanish.** For memory `{1}` over `F_2^n`, `tau` is a permutation of
`F_2^n` and (Section 6.2 of `formal-polynomial-strict-pairs-2026-09-12.md`) is a
composite of edge shears `x_i -> x_i + f(x_{-i})`, each a formal involution. So
`hat tau^*` is an automorphism of `R`, `hat tau^*|_I` is bijective,
`coker(hat tau^*|_I) = 0`, and `[eps] = 0`. This recovers formalizability of every
sitewise pair from the cokernel picture.

The content of the reformulation: the search over enlarged memories and all
representatives collapses to solving **one** `F_2`-linear equation
`hat tau^*(delta) = eps` inside `I`, for a single fixed representative of `tau`.

## 3. The conormal quotient is free, and `hat tau^*` acts by the Jacobian

Filter `I` by the `I`-adic filtration. The conormal module `I/I^2` is where the
leading part of the obstruction lives, and it is computable.

> **Lemma 2.** The de Rham differential `d : I/I^2 -> Omega_{R/F_2} (x)_R B` is an
> isomorphism onto the free `B`-module `(+)_h B dX_h`, sending `u_h := X_h^2 + X_h`
> to `dX_h`.

*Proof.* For the surjection `R -> B = R/I` the cotangent sequence gives an exact
`I/I^2 --d--> Omega_R (x) B -> Omega_B -> 0`. `B` is etale-trivial over `F_2` in the
sense that `Omega_{B/F_2} = 0`: every element of `B` is idempotent, so
`0 = d(y^2) = 2y\,dy = 0` gives no relation directly, but `y = y^2` gives
`dy = d(y^2) = 2y\,dy = 0` in characteristic `2`; hence `Omega_B = 0`. So `d` is
onto the free module `(+)_h B dX_h`. On generators
`d(u_h) = d(X_h^2 + X_h) = (2X_h + 1) dX_h = dX_h` in characteristic `2`. These are a
free basis, so `d` is injective on the classes `u_h` and `I/I^2` is free on `{u_h}`,
with `d` the stated isomorphism. QED

> **Proposition 3.** Under the isomorphism of Lemma 2, the map induced by `hat tau^*`
> on `I/I^2` is the reduced Jacobian: in the basis `{u_h}`,
> `hat tau^*(u_h) = sum_{h'} (partial hat mu_h / partial X_{h'} mod I) u_{h'}`.

*Proof.* `hat tau^*(u_h) = hat mu_h^2 + hat mu_h`. Apply `d` and Lemma 2:
`d(hat mu_h^2 + hat mu_h) = (2 hat mu_h + 1) d hat mu_h = d hat mu_h =
sum_{h'} (partial hat mu_h/partial X_{h'}) dX_{h'}`, and reduce coefficients mod `I`.
Transport back along `d^{-1}`. QED

So on the conormal quotient `hat tau^*` is the `B`-linear operator with matrix the
Boolean-reduced Jacobian `J_B = (partial hat mu_h/partial X_{h'} mod I)`, an
equivariant finite-memory element of `M_n(B rtimes G)` (`n` tracks, `G`-translation).

**Constant specialization is the Kaplansky matrix.** Evaluating the Boolean entries
at a constant configuration `c in F_2^n`, and using equivariance, `J_B` specializes
to `J_tau(c) = sum_m (partial mu / partial X_m)(c) delta_m in M_n(F_2[G])`, the exact
linearization of Theorem 1 of `formal-polynomial-strict-pairs-2026-09-12.md`. In
particular the `c = 0` (or any constant) specialization of the conormal map is the
matrix whose one-sided invertibility is a direct-finiteness / Kaplansky statement for
`M_n(F_2[G])`.

> **Corollary 4 (leading obstruction).** The image of `[eps]` in
> `coker(hat tau^*|_{I/I^2}) = coker(J_B on (+)_h B dX_h)` is the leading part of the
> formalizability obstruction. It vanishes if `J_B` is surjective as a
> `B rtimes G`-operator. Its constant specialization is
> `coker(J_tau(c) : F_2[G]^n -> F_2[G]^n)`, which is `0` exactly when `J_tau(c)` is a
> split epimorphism over `F_2[G]` — the linear/Kaplansky layer.

This is the precise sense in which the formalizability obstruction *meets* Kaplansky:
its top graded piece is a Jacobian cokernel over the Boolean group ring, and the
constant slice of that is the matrix `M_n(F_2[G])` cokernel of Theorem 1. Higher
`I`-adic pieces are corrections layered on top, governed by the same operator
`hat tau^*` restricted to `I^k/I^{k+1}`, each a free `B`-module by the same de Rham
computation applied to symmetric powers (not carried out here).

## 4. What is and is not decided

**Decided.**
- Formalizability is exactly `[eps] = 0` in `coker(hat tau^*|_I)`, a single linear
  solvability question over `I` for one fixed representative of `tau` (Prop 1).
- The class depends only on the functions once `hat tau^*` is fixed; sitewise pairs
  give `0` (Section 2).
- The conormal quotient is free on `{u_h}` and `hat tau^*` acts by the reduced
  Jacobian; the leading obstruction is a Jacobian cokernel over `B rtimes G` whose
  constant slice is the `M_n(F_2[G])` Kaplansky cokernel (Lemma 2, Prop 3, Cor 4).

**Not decided.**
- Whether `[eps] = 0` for every left-invertible pair, i.e.
  `binary-left-inverse-pairs-are-formalizable`. Prop 1 turns this into: is
  `eps_h in hat tau^*(I)` for some `tau`-lift? A negative instance is a pair whose
  leading class in `coker(J_B)` is nonzero and stays nonzero under every change of
  `tau`-representative — equivalently a Boolean-Jacobian cokernel that no lift kills.
- Whether the obstruction depends on the `tau`-representative or only on the tables.
  Section 2 fixes independence on the `sigma` side; the `tau` side is open, because a
  different `tau`-lift changes both `hat tau^*|_I` and `eps`.

**Handoff.** The nonvanishing hunt is now a concrete `F_2[G]`-module computation:
exhibit a finite-memory injective non-surjective `tau` whose reduced Jacobian `J_B`
has `eps` outside its image in `coker(J_B on (+) B dX)`. On a host with `M_n(F_2[G])`
directly finite the constant slice is not enough (it is a split epi there), so any
witness must live in the higher `I`-adic layers — exactly the collapse-essential
regime of Section 4 of `formal-polynomial-strict-pairs-2026-09-12.md`.
