---
rg: 2
id: thompson-v-gap-witnesses-need-unbounded-lie-closure
kind: claim
title: Low-defect irreducibles of S4 *_Z2 S3 are primitive, Lie-irreducible and have closures with unbounded derived algebra; nontrivial irreducibles whose closure has derived algebra of dimension at most N have defect at least min(1/2, delta_N/2)
distinct_from:
  thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes: that reduces V not MF to a uniform gap over all nontrivial irreducibles of G0 and proves each fixed dimension is gapped; this proves a gap that is uniform in the dimension n on the subclass whose Zariski-type invariant, the dimension of the derived algebra of the closure of the image, is bounded, and proves that witnesses of small defect are primitive and restrict irreducibly to the identity component of their closure.
  finite-image-higman-models-collapse-opnorm: that treats tuples generating a finite group for Higman's group, with defect measured on relators of an arbitrary tuple; this treats exact representations of the virtually free G0 with arbitrary (typically infinite, dense in a compact Lie group) image, and its engine is the adjoint representation of the closure, not a Zassenhaus contraction inside a finite group.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that is the exact statement D = 0 implies trivial; this is a quantitative lower bound depending only on the Lie algebra of the closure.
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that amplifies witnesses by tensor powers; this shows that amplification from a fixed compact group (tensor powers, Schur functors, Sym^m of a fixed representation) cannot produce MF witnesses for V at all.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the analogous reduction for T; this is a partial gap theorem for V's G0.
artifacts:
  - experiments/thompson-v-lie-closure-gap-2026-09-17/check_adjoint_transfer.py
  - experiments/thompson-v-lie-closure-gap-2026-09-17/out_check_adjoint_transfer.txt
---

**ESTABLISHED** by `thompson-v-gap-witnesses-need-unbounded-lie-closure-proof` (written proof,
unreviewed).

## Setting

Notation as in `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes`:

```text
G0 = S4 *_<a> S3 = < a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3 >,      V = G0 / << r5, r6, r7, r8 >>,
D(rho) = max_(5 <= i <= 8) || rho(r_i) - 1 ||_op ,       delta_n = min{ D(sigma) : sigma nontrivial irreducible, dim sigma <= n }.
```

For a finite-dimensional unitary representation `sigma : G0 -> U(n)` let `K_sigma` be the closure of
`sigma(G0)` in `U(n)`. It is a compact Lie group. Let `K_sigma^0` be its identity component,
`l_sigma = Lie(K_sigma)`, a real subalgebra of `u(n)`, and

```text
N_sigma = dim_R [l_sigma, l_sigma] .
```

By standard structure theory this is `dim [K_sigma^0, K_sigma^0]`, the dimension of the semisimple part.
The proof does not use this. `N_sigma = 0` iff `K_sigma^0` is abelian. Also `N_sigma <= n^2 - 1`, since `[l_sigma, l_sigma]`
lies in `su(n)`.

Put `delta_0 = 2`. Then `delta_N` is nonincreasing in `N >= 0` and positive, by item 1 of the reduction.

## Statement

Let `sigma` be a nontrivial finite-dimensional unitary representation of `G0`.

1. **(Imprimitive models die at sqrt 2.)** Suppose `C^n = E_1 (+) ... (+) E_k` is an orthogonal
   decomposition into nonzero subspaces that `sigma(G0)` permutes, and the permutation action of `G0`
   on `{E_1, ..., E_k}` is nontrivial. Then `D(sigma) >= sqrt 2`. In particular:
   - (1a) every nontrivial `sigma` that is **monomial** in some orthonormal basis (each `sigma(g)` a
     permutation matrix times a diagonal unitary, the "torus regauge" ansatz with arbitrary phases)
     has `D(sigma) >= sqrt 2`;
   - (1b) every `sigma = Ind_H^(G0) tau` induced from a subgroup `H` of finite index `>= 2` has
     `D(sigma) >= sqrt 2`;
   - (1c) if `sigma` is irreducible and `D(sigma) < sqrt 2`, then `sigma` restricted to `K_sigma^0` is
     isotypic, and the centre `Z(K_sigma^0)` acts by scalars.
2. **(Virtually abelian images die at 1/2.)** If `sigma` is irreducible and `sigma(G0)` is finite modulo
   scalars, or more generally `sigma(G0)` is virtually abelian, or more generally `K_sigma^0` is abelian,
   then `D(sigma) >= 1/2`. This includes every finite-image representation.
3. **(Adjoint transfer.)** If `sigma` is irreducible, then

   ```text
   D(sigma) >= min( 1/2 , delta_(N_sigma) / 2 ).
   ```

   So for every `N` the constant `c_N = min(1/2, delta_N/2) > 0` is a lower bound for `D(sigma)`
   over **all** nontrivial irreducibles with `N_sigma <= N`, **in every dimension `n`**.
4. **(Lie-irreducibility.)** If `sigma` is irreducible and `D(sigma) < 1/4`, then `sigma` restricted
   to `K_sigma^0` is irreducible. Equivalently, `sigma` is not of the form `tau~ (x) pi` with `pi` a
   projective representation of dimension `>= 2` that is trivial on `K_sigma^0`.

## Consequences for `thompson-v-is-not-mf`

- **Shape of any MF witness.** By item 3 of the reduction, `V` is MF iff there are nontrivial
  irreducibles `sigma_j` of `G0` with `D(sigma_j) -> 0`. By (1)-(4), for all large `j`, `sigma_j`
  is primitive, `K_(sigma_j)^0` is nonabelian, `sigma_j` restricted to `K_(sigma_j)^0` is
  irreducible (so the connected semisimple group `[K^0, K^0]` already acts irreducibly), and
  **`N_(sigma_j) -> infinity`**.
- **Fixed-group amplification is dead.** Let `M` be any compact Lie group, `phi : G0 -> M` any
  homomorphism and `pi` any finite-dimensional unitary representation of `M`. If `pi o phi` is
  nontrivial, then `D(pi o phi) >= c_(dim M)`. So tensor powers, Schur functors, `Sym^m`,
  highest-weight towers of a fixed representation, and all representations of a fixed compact group
  pulled back along one map, are uniformly gapped, independently of their dimension.
- **Transfer inequality.** For every nontrivial irreducible `sigma` with `D(sigma) < 1/2`, the adjoint
  action of `G0` on `[l_sigma, l_sigma]_C` is a nontrivial representation of dimension `N_sigma` with
  defect at most `2 D(sigma)`. Any witness sequence therefore produces a second witness sequence
  made of the adjoint representations of its closures.
- **Invariant and death step.** The invariant is `N_sigma`, the dimension of the derived algebra of
  the closure. In every model class where it stays bounded, the argument fails at the same step: the
  adjoint representation of the closure is a nontrivial representation of `G0` of dimension at most
  `N` with defect at most `2D`, and it is gapped by `delta_N`.
- **What survives.** Primitive, Lie-irreducible representations whose closures have semisimple part
  of unbounded dimension. For example, `sigma_j` with Zariski-dense image in `U(n_j)`, or in a
  simple subgroup of dimension going to infinity. A proof of the hole must bound `D` on exactly this
  class. A disproof must produce such a sequence.

## Remarks (not claimed)

- The only inputs about `V` are that it has no nontrivial finite quotient and no nontrivial
  character. The same argument therefore gives the analogous partial gaps for `T` over
  `Z4 * Z3` (`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`). There the character step needs
  that nontrivial characters of `Z4 * Z3` that do not factor through `T` have defect at least
  `2 sin(pi/12) > 1/2` on some relator.
- Let `G = G0'/<<R>>` with `R` finite and `G` without nontrivial finite quotient, and measure the defect
  of exact representations of `G0'` on `R`. Then the proofs of (1) (except the character step in
  (1a)), (1b), (1c) and (4) go through verbatim.
