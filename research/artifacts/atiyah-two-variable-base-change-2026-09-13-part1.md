# Two transcendental coefficients under the determinant conjecture, part 1

Lane `ex2-atiyah-base-change-td2`, 2026-09-13. Continues
`research/artifacts/atiyah-one-variable-base-change-2026-09-12.md` (Theorem 3,
properties (D1)-(D3), (UB)) and
`research/artifacts/atiyah-transcendence-degree-one-base-change-2026-09-13.md`
(Theorem 4). Part 1: statement, the jump locus, the reduction. Part 2: the cycle
inequality. Part 3: the Diophantine construction and the conclusion.
**Unreviewed.**

## 0. Theorem 5

Let `G` be torsion-free, satisfying Strong Atiyah over `Qbar` and Lueck's
determinant conjecture. Put `D = D_(Qbar[G])` (a skew field, by Linnell's
criterion) and let `D(x_1, x_2)` be the Ore skew field of fractions of
`D[x_1, x_2]`, equivalently `D(x_1)(x_2)`, with `x_1, x_2` central.

1. For every `z = (z_1, z_2) in C^2` with `z_1, z_2` algebraically independent
   over `Qbar`, and every `m x n` matrix `A(x)` over `Qbar[G][x_1, x_2]`,
   `dim_G ker A(z) = n - rk_(D(x_1,x_2)) A`. In particular every matrix over
   `Qbar(z_1, z_2)[G]` has integral kernel dimension.
2. These dimensions are the same at all such `z`. This is Galois invariance for
   automorphisms of `C` fixing `Qbar`, restricted to transcendence degree 2.

The proof never approximates `G`. Its new inputs, beyond Theorem 3, are:
* an integral model attached to a zero-dimensional cycle over `Q` (Part 2);
* a Chow form with a small value, built from one small bivariate irreducible
  polynomial and one small one-variable polynomial, which are automatically
  coprime (Part 3).

Transversality problems never arise.

Notation: `Delta(T) = exp (tau (x) Tr)(log |T|)`, as in the one-variable
artifact. `k_A(w) = dim_G ker A(w)` for `w in C^2`.

## 1. The algebraic jump locus is contained in a proper Zariski-closed set

**Lemma J.** Let `A` be `m x n` over `Qbar[G][x_1, x_2]`, of rank `r` over
`D(x_1, x_2)`. There is a proper Zariski-closed `Y_A ⊂ A^2`, defined over
`Qbar`, with `k_A(beta) = n - r` for every `beta in Qbar^2 \ Y_A`.

*Proof.*
* **Normal form.** `R = D(x_1)[x_2]` is a polynomial ring over a skew field in
  a central variable, hence a left and right principal ideal domain. So
  `A = P diag(e_1, ..., e_r, 0, ..., 0) Q` with `P in GL_m(R)`,
  `Q in GL_n(R)` and nonzero `e_i in R`.
* **Evaluating `D(x_1)` at central points.** For `beta_1 in Qbar` the
  Laurent series field `D((x_1 - beta_1))` is a skew field containing
  `D[x_1]`. By the universal property of Ore localization `D(x_1)` embeds in it.
  - An element `a b^-1` with `b in D[x_1]`, `b(beta_1) != 0`, lies in
    `D[[x_1 - beta_1]]`, because `b` is a unit there.
  - Taking the constant term is a ring homomorphism on `D[[x_1 - beta_1]]`.
    On `D[x_1]` it is evaluation.
  - A nonzero `b in D[x_1]` has at most `deg b` central roots. If
    `b(beta) = 0` then `b = (x_1 - beta) b'`, and `b'` vanishes at every other
    central root, since `x_1 - beta'` is central.
* **The bad lines.** Write every entry of `P, P^-1, Q, Q^-1` and every
  coefficient of every `e_i` with one common right denominator `b in D[x_1]`
  (right Ore condition). Let `B_0` be the finite set of central roots of `b`.
  For `beta_1 notin B_0`, the constant-term map sends `P, P^-1` to mutually
  inverse matrices over `D[x_2]`. So
  `A(beta_1, x_2) = P(beta_1) diag(e_i(beta_1, x_2)) Q(beta_1)`.
* **Where `e_i` vanishes.** Write `e_i = sum_k a_ik b^-1 x_2^k` with
  `a_ik = sum_l a_ikl x_1^l`, `a_ikl in D`. Then
  `e_i(beta_1, beta_2) = (sum_(k,l) a_ikl beta_1^l beta_2^k) b(beta_1)^-1`,
  because `beta_2` is central.
  - Choose a `Qbar`-basis `d_1, ..., d_t` of the span of the `a_ikl`, and write
    `a_ikl = sum_j c_iklj d_j` with `c_iklj in Qbar`.
  - Then `e_i(beta) = 0` exactly when the polynomials
    `f_ij = sum_(k,l) c_iklj x_1^l x_2^k` all vanish at `beta`. Some `f_ij` is
    nonzero, because `e_i != 0`.
* **Conclusion.** Put `Y_A = (B_0 x A^1) ∪ ⋃_i V(f_i1, ..., f_it)`. For
  `beta notin Y_A`, `A(beta) in M(Qbar[G])` is equivalent over `D` to
  `diag(e_1(beta), ..., e_r(beta), 0, ...)` with all `e_i(beta)` units of `D`.
  So `rk_D A(beta) = r`, and by Strong Atiyah over `Qbar` (Linnell's criterion)
  `k_A(beta) = n - r`. ∎

The finitely many coefficients `c_iklj` lie in a number field. The union
`Y_A^Q` of the Galois conjugates of `Y_A` is proper, Zariski-closed and defined
over `Q`. A point with algebraically independent coordinates lies on no proper
subvariety defined over `Qbar`, so it is not in `Y_A^Q`.

**Lemma L (the generic rank bounds the kernel everywhere).** For every
`w in C^2`, `k_A(w) >= n - r`.

*Proof.* `k_A` is upper semicontinuous in `w`, by Lemma 4 of the Liouville
artifact, since `A(w)` depends norm-continuously on `w`. Algebraic points off
`Y_A` are dense in `C^2`, and `k_A = n - r` there. So
`k_A(w) >= limsup k_A(w') = n - r`. ∎

## 2. Reduction to a square integral pencil with a kernel at `z`

Suppose `z` has algebraically independent coordinates and some `A` has excess
`kappa = k_A(z) - (n - r) > 0`. By Lemma L the excess is never negative.

* **(R1') Linearization.** Write `A = A_0 + x_1 B_1(x) + x_2 B_2(x)`. Higman's
  identity, with `a = A_0 + x_1 B_1`, `b = x_2 I`, `c = B_2`, gives
  `A (+) I ~ [[A_0 + x_1 B_1, x_2 I], [-B_2, I]]` over `Qbar[G][x]` by
  elementary matrices. Repeat in both variables until the pencil is linear. The
  equivalences specialize to invertible matrices at every point, and generic
  ranks shift by the size of the identity block. So the excess is unchanged.
* **(R2') Square and full.** This is (R2) of the one-variable artifact
  verbatim, over `D(x_1, x_2)`. Choose pivots on the generic kernel (`W`) and a
  completion of the generic image (`Y`), and put `M = [[L, Y], [W, 0]]`. Then
  `M` is full over `D(x_1, x_2)` and `k_M(z) >= kappa`.
* **(R3') Integral coefficients.** Scale into `O_F` for a number field `F`,
  and restrict scalars along a `Z`-basis of `O_F`. The pencil `rho(M)` is over
  `Z[G]`.
  - `rho(M)(z)` is similar, by an invertible scalar matrix independent of `x`,
    to `(+)_sigma M^sigma(z)`. Its generic rank is the sum of the generic ranks
    of the `M^sigma`, since the similarity has entries in `Qbar ⊂ D`.
  - By Lemma L each `M^sigma` has excess `>= 0` at `z`. So `rho(M)` has excess
    `>= kappa`.
  - Apply (R2') again, with 0-1 coordinate matrices.

**Output.** `M(x) = M_0 + x_1 M_1 + x_2 M_2` with `M_i in M_N(Z[G])`, full
over `D(x_1, x_2)`, with `kappa_0 := k_M(z) >= 1`, and a proper Zariski-closed
`Y := Y_M^Q` over `Q` with `z notin Y` such that `M(beta)` is injective for
every `beta in Qbar^2 \ Y`.

Theorem 5.1 follows once `M(z)` is shown to be injective for every such `M`.
Then `kappa = 0` for every `A`. Theorem 5.2 follows, because
`n - rk_(D(x)) A` does not depend on `z`. Parts 2 and 3 derive a contradiction
from `kappa_0 >= 1`.
