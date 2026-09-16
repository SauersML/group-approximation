# Jensen's inequality for ordered group algebras and the determinant conjecture

Date: 16 September 2026 (swarm agent `hi-spec-determinant-conjecture`, angle
special case / strengthening). Written proofs, no machine verification except the
finite check in Section 7. The one external input is Jensen's inequality for
finite maximal subdiagonal algebras (Section 1.3), imported through the claim
`jensen-inequality-for-finite-subdiagonal-algebras`.

**Contents.**

- Section 1: conventions and the cited input.
- Section 2: a subdiagonal algebra from an invariant random order. The
  deterministic special case gives Arveson's algebra for a left-ordered group.
- Section 3: Theorem A, the left-orderable case.
- Section 4: Theorem B, the random-order case, in matrix form.
- Section 5: the bijection criterion, and an obstruction for small supports.
- Section 6: remarks and extensions.
- Section 7: a non-left-orderable example (Hantzsche--Wendt group).
- Section 8: novelty, with the sources checked.
- Section 9: attempts that failed.

## 1. Conventions and the cited input

### 1.1 Operators

`G` is a countable discrete group. On `l^2(G)`:

- `lambda(g) delta_h = delta_(gh)` and `rho(g) delta_h = delta_(h g^-1)`;
- `L(G) = lambda(G)''`, with trace `tau(T) = <T delta_e, delta_e>`;
- for `x = sum x(g) g` in `C[G]`, `x^* = sum conj(x(g)) g^-1` and
  `lambda(x) = sum x(g) lambda(g)`.

For a finite von Neumann algebra `M` with faithful normal tracial state `tau`,
`M_n(M)` carries the normalized trace `tau_n(T) = (1/n) sum_i tau(T_ii)`.

**Determinants.** Two determinants appear.

- *Unregularized (Fuglede--Kadison).* For `T in M_n(M)`,

  ```text
  Delta(T) = exp tau_n( log |T| ) = exp integral_[0,infinity) log t  d nu_|T|(t)  in [0, infinity),
  ```

  where `nu_|T|` is the spectral distribution of `|T|` under `tau_n`. The integral
  is `-infinity`, and `Delta(T) = 0`, if `nu_|T|` has an atom at `0` or `log t`
  is not integrable near `0`. This is the definition used by Blecher--Labuschagne
  ("exp tau(log|a|) if |a| is strictly positive, and otherwise inf Delta(|a| +
  eps 1)"). Monotone convergence identifies the two forms.
- *Regularized (Lück).* For a morphism `f` of finitely generated Hilbert
  `N(G)`-modules, `det_N(G)(f) = exp integral_(0,infinity) log t dF_f(t)` if the
  integral is finite, and `0` otherwise. Here `F_f` is the spectral density
  function of `f`, the kernel is excluded, and the trace is the unnormalized
  `sum_i tau(T_ii)`. By convention `det(0) = 1`.

For `T` in `M_n(L(G))` viewed as an endomorphism of `l^2(G)^n`:

```text
if Delta(T) > 0 then ker T = 0, and det_N(G)(T) = Delta(T)^n.            (1.1)
```

Two elementary facts are used repeatedly.

- `det_N(G)(f) = det_N(G)(f^*) = det_N(G)(f^* f)^(1/2)`. The spectral density
  of `f^* f` is that of `f` with the variable squared, and `f^* f`, `f f^*`
  agree away from `0` by polar decomposition.
- `Delta(U T V) = Delta(T)` for unitaries `U`, `V`, since `|UTV| = V^*|T|V`.

### 1.2 Right multiplication versus `lambda`

Lück's determinant conjecture concerns `r_A : l^2(G)^m -> l^2(G)^n`, right
multiplication of row vectors by `A in M_(m x n)(Z[G])`. Two facts:

- `r_(AB) = r_B r_A` and `r_A^* = r_(A^*)`, so `r_A^* r_A = r_(A A^*)`.
- For `u in C[G]`, `r_u = sum u(g) rho(g^-1)`.

Let `J` be the antiunitary `J(sum c_g delta_g) = sum conj(c_g) delta_(g^-1)`.

- Then `J lambda(g) J = rho(g)` and `J lambda(u) J = r_(u^*)`.
- For square `X in M_n(C[G])`, acting on column vectors, `r_X` has `(j,i)` entry
  `r_(X_ij)`. With `J_n = J (+) ... (+) J`, this gives `J_n r_X J_n = lambda_n(X^*)`,
  where `lambda_n(Y) = [lambda(Y_ij)]`.
- `J_n` conjugation carries real functional calculus to real functional
  calculus. It also preserves traces of positive elements, because
  `<J T J delta_e, delta_e> = <delta_e, T delta_e>` is real.

Hence, using `det(f) = det(f^*)`,

```text
det_N(G)(r_X) = det_N(G)(lambda_n(X^*)) = det_N(G)(lambda_n(X)).            (1.2)
```

### 1.3 The cited input: Jensen's inequality

A *tracial subalgebra* of `(M, tau)` is a weak*-closed unital subalgebra `A`
such that the unique `tau`-preserving conditional expectation
`Phi : M -> D := A cap A^*` is multiplicative on `A`. A *finite maximal
subdiagonal algebra* is a tracial subalgebra with `A + A^*` weak*-dense in `M`.
These are the definitions of Blecher--Labuschagne, arXiv:math/0611879, Section 1.

**Jensen's inequality (cited).** If `A` is a finite maximal subdiagonal algebra
in `(M, tau)` with expectation `Phi`, then

```text
Delta(Phi(a)) <= Delta(a)          for every a in A.                      (J)
```

Provenance: Labuschagne, Proc. AMS 133 (2005) 3643--3646, Theorem 3, proved
Jensen's formula for all maximal subdiagonal algebras, and Arveson (Amer. J. Math.
89 (1967)) showed the formula implies (J). Blecher--Labuschagne record this
with the display `Delta(Phi(a)) <= Delta(a), a in A`. Austin, arXiv:2412.13751,
Proposition 4.5, uses it in the same way. See
`jensen-inequality-for-finite-subdiagonal-algebras-citation` for verbatim quotes
and read dates. Labuschagne's paper itself was not fetched.

Uses in this artifact:

- (J) with `D = C` and `Phi = tau(.) 1`, where it reads `Delta(a) >= |tau(a)|`;
- (J) for `M_n` of such an algebra;
- (J) for crossed products `L^infinity(Omega) x| Gamma`.

**Matrix amplification.** If `A` is finite maximal subdiagonal in `M` with
expectation `Phi`, then `M_n(A)` is finite maximal subdiagonal in
`(M_n(M), tau_n)` with expectation `Phi_n = [Phi(.)]`:

- `M_n(A)` is a weak*-closed unital subalgebra;
- `M_n(A) cap M_n(A)^* = M_n(A cap A^*) = M_n(D)`, because
  `(x^*)_ij = (x_ji)^*`;
- `Phi_n` is a faithful normal `tau_n`-preserving conditional expectation onto
  `M_n(D)`, so it is the unique one;
- `Phi_n(xy)_ij = sum_k Phi(x_ik) Phi(y_kj) = (Phi_n(x) Phi_n(y))_ij`;
- `M_n(A) + M_n(A)^* = M_n(A + A^*)` is weak*-dense in `M_n(M)`.

**Determinants on the diagonal.**

- For `D = C` and `C in M_n(C)` with trace `(1/n) tr`: `Delta(C) = |det C|^(1/n)`.
- For `D = L^infinity(Omega, mu)` and `F in M_n(L^infinity(mu))`:
  `Delta(F) = exp (1/n) integral log |det F(omega)| d mu(omega)`.

## 2. The subdiagonal algebra of an invariant random order

This is a variant of Austin, arXiv:2412.13751, Lemma 4.3. Austin uses the
"past" `{g <= e}` where we use the "future" `{e <= g}`, and works with
C*-crossed products; we verify the von Neumann algebra version directly.

### 2.1 Setting

`Gamma` is a countable group and `Omega` is the compact metrizable space of strict
total orders on `Gamma`, a closed subset of `{0,1}^(Gamma x Gamma)`.

- **Action.** `Gamma` acts by `a <_(g omega) b  iff  g^-1 a <_omega g^-1 b`.
  Equivalently `g a <_(g omega) g b iff a <_omega b`, and this is a left action.
- **Invariant random order.** A `Gamma`-invariant Borel probability measure `mu`
  on `Omega`.
- **Minima.** For finite nonempty `A` in `Gamma`, `min_omega A` is the least element
  of `A` for `omega`, and

  ```text
  min_(g omega)(g A) = g min_omega(A).                                     (2.1)
  ```

- **Crossed product.** `M = L^infinity(Omega, mu) x|_alpha Gamma`, with
  `alpha_g(f)(omega) = f(g^-1 omega)`. It is generated by `L^infinity(mu)` and
  unitaries `u_g` with `u_g f u_g^* = alpha_g(f)`, realized on
  `L^2(mu) (x) l^2(Gamma)`. Note `supp alpha_g(f) = g supp f`.
- **Trace and expectation.** `tau(f u_g) = delta_(g,e) integral f dmu` is a
  faithful normal tracial state (invariance of `mu`). The canonical
  `E : M -> L^infinity(mu)`, `E(sum f_g u_g) = f_e`, is a faithful normal
  `tau`-preserving conditional expectation.
- **Fourier coefficients.** Every `y in M` has `y_g := E(y u_g^*)`, and `y` is
  determined by `(y_g)_g`. Each map `y -> y_g` is weak*-continuous, and
  `E(u_g^* x u_g) = alpha_(g^-1)(E(x))`.
- **Group algebra.** `u_g <-> lambda(g)` embeds `L(Gamma)` in `M`
  trace-preservingly, so determinants of elements of `M_n(L(Gamma))` computed in
  `M_n(M)` agree with those computed in `M_n(L(Gamma))`.

### 2.2 The algebra

For `g in Gamma` put `S_g = {omega : e <=_omega g}`, so `S_e = Omega`. Let
`A_0` be the linear span of all `f u_g` with `f in L^infinity(mu)` vanishing
a.e. off `S_g`, and let `A` be its weak*-closure.

**Proposition 2.1.** `A` is a finite maximal subdiagonal algebra in `(M, tau)`
with `A cap A^* = L^infinity(mu)` and expectation `E`.

*Proof.* We check the four conditions.

**(i) `A` is a unital algebra.**

- `u_e = 1` lies in `A_0`.
- Let `f` vanish off `S_g` and `h` vanish off `S_k`. Then
  `(f u_g)(h u_k) = f alpha_g(h) u_(gk)`, and `f alpha_g(h)` vanishes off
  `S_g cap g S_k`.
- By the definition of the action, `g S_k = {omega : g <=_omega gk}`.
- By transitivity `S_g cap g S_k` lies in `{e <= gk} = S_(gk)`.
- So `A_0` is an algebra, and so is its weak*-closure, since multiplication is
  separately weak*-continuous.

**(ii) `E` is multiplicative on `A`.** With `f`, `h` as in (i), the product
`E((f u_g)(h u_k)) = delta_(gk,e) f alpha_g(h)`.

- Suppose `k = g^-1` and `g != e`. Then `f alpha_g(h)` vanishes off
  `{e <= g} cap {g <= e}`, which is empty. So the product is `0`, which equals
  `E(f u_g) E(h u_k)`.
- If `g = k = e` both sides are `f h`.
- By bilinearity `E(ab) = E(a)E(b)` on `A_0`.
- Since `E` is normal and multiplication separately weak*-continuous, the
  identity passes to `A`, first in one variable and then in the other.

**(iii) `A + A^*` is weak*-dense.** Take `f in L^infinity(mu)` and `g in Gamma`,
and write `f u_g = f 1_(S_g) u_g + f 1_(S_g^c) u_g`.

- The first term lies in `A_0`.
- For the second, `(f 1_(S_g^c) u_g)^* = alpha_(g^-1)(conj(f) 1_(S_g^c)) u_(g^-1)`.
- This vanishes off `g^-1 S_g^c = g^-1 {g <_omega e} = {e < g^-1}`, which lies in
  `S_(g^-1)`. So the adjoint lies in `A_0`.
- The span of all `f u_g` is weak*-dense in `M`.

**(iv) `A cap A^* = L^infinity(mu)`.** The inclusion `supseteq` is clear.
Conversely let `y in A cap A^*`.

- For `y in A_0`, `y_g` vanishes off `S_g`. The set of such functions is
  weak*-closed and `y -> y_g` is weak*-continuous, so the same holds for all `y` in
  `A`.
- Apply this to `y^* in A`. Its coefficients are
  `(y^*)_(g^-1) = E(y^* u_g) = E(u_g^* y)^* = alpha_(g^-1)(E(y u_g^*))^* = alpha_(g^-1)(conj(y_g))`,
  since `u_g^* y = u_g^* (y u_g^*) u_g`.
- This vanishes off `S_(g^-1)`, so `y_g` vanishes off
  `g S_(g^-1) = {g <= e}`.
- For `g != e` the sets `{e <= g}` and `{g <= e}` are disjoint, so `y_g = 0`.
  Hence `y = y_e` lies in `L^infinity(mu)`.

Finally `E` is the faithful normal `tau`-preserving conditional expectation onto
`A cap A^*`, so it is the unique one. ∎

**Corollary 2.2 (left orders).** Let `P` be the positive cone of a
left-invariant order `<` on `G`, so `G = P ⊔ {e} ⊔ P^-1`, `PP ⊆ P` and
`a < b iff a^-1 b in P`. Then:

- the weak*-closure `A_P` of `span lambda(P ∪ {e})` is a finite maximal
  subdiagonal algebra in `L(G)`, with `D = C` and `Phi = tau(.) 1`;
- every `M_n(A_P)` is one in `M_n(L(G))`, with `Phi_n(T) = [tau(T_ij)]`.

*Proof.* Take `mu = delta_<`. This is invariant because `g.< = <` for a
left-invariant order. Then:

- `L^infinity(mu) = C` and `M = L(G)`;
- `S_g` is `Omega` (identified with the point `<`) if `g in P ∪ {e}`, and is null
  otherwise, so `A = A_P`.

The matrix statement is the amplification in Section 1.3. This recovers the
example of Arveson (1967), Section 3.2, as quoted in Blecher--Labuschagne,
arXiv:math/0611879, p. 4. ∎

## 3. Theorem A: left-orderable groups

Throughout this section `G` is left-orderable with positive cone `P` and left
order `<`. The right-invariant order with the same cone is `a <' b iff b a^-1 in P`.

**Theorem A.**

**(a) One by one.** Let `x in C[G]` be nonzero, and let `g_0` be the `<`-minimum
of `supp x` (or its `<`-maximum). Then

```text
Delta(lambda(x)) >= |x(g_0)| > 0.
```

So `lambda(x)` and `r_x` are injective with dense range, and
`det_N(G)(r_x) >= |x(g_0)|`. If `x in Z[G]` is nonzero then `det_N(G)(r_x) >= 1`.

**(b) Square matrices with nonsingular leading coefficients.** Let
`X in M_n(C[G])`. Suppose there are `g_1, ..., g_n, h_1, ..., h_n in G` with

```text
supp X_ij ⊆ g_i (P ∪ {e}) h_j        for all i, j,
```

and put `L_ij = X_ij(g_i h_j)`. Then

```text
det_N(G)(r_X) >= Delta(lambda_n(X))^n >= |det L|.
```

If `det L != 0` then `r_X` is injective with dense range. If moreover `X` is
integral, `det_N(G)(r_X) >= 1`. Two special cases:

- *Rows.* `h_j = e` and `g_i = min_< (union_j supp X_ij)`, so `L_ij` is the
  coefficient of `X_ij` at the leading element of row `i`.
- *Columns.* `g_i = e` and `h_j = min_<' (union_i supp X_ij)`.

**(c) Rectangular rows and columns.** For every `A in M_(1 x n)(Z[G])` and every
`A in M_(n x 1)(Z[G])`, `det_N(G)(r_A) >= 1`.

**(d) Spectral consequence.** Let `x = x^* in Z[G]` with `x` not in `Z 1`, and let
`mu_x` be its spectral measure on `R` with respect to `tau`. Then:

- `mu_x` has no atoms;
- `integral log |Q(t)| d mu_x(t) >= 0` for every nonzero `Q in Z[t]`, that is,
  `mu_x` obeys every Serre inequality.

*Proof of (a).* Put `y = g_0^-1 x`, so `supp y ⊆ g_0^-1 supp x ⊆ P ∪ {e}`, because
`g_0 <= h` means `g_0^-1 h in P ∪ {e}`.

- So `lambda(y) in A_P` and `tau(lambda(y)) = y(e) = x(g_0)`.
- By (J) for `A_P` (Corollary 2.2, `Phi = tau(.) 1`),
  `Delta(lambda(y)) >= Delta(tau(lambda(y)) 1) = |x(g_0)|`.
- `lambda(x) = lambda(g_0) lambda(y)` with `lambda(g_0)` unitary, so
  `Delta(lambda(x)) = Delta(lambda(y))`.
- For the maximum, apply the same argument to the reversed order, which is left
  invariant with cone `P^-1`.

`Delta(lambda(x)) > 0` forces `ker lambda(x) = 0`. In the finite von Neumann
algebra `L(G)` an injective element has dense range. By (1.1) and (1.2),
`det_N(G)(r_x) = det_N(G)(lambda(x)) = Delta(lambda(x))`. For integral `x`,
`|x(g_0)| >= 1`. ∎

*Proof of (b).* Put `Y_ij = g_i^-1 X_ij h_j^-1`.

- Then `supp Y_ij ⊆ P ∪ {e}`, so `lambda_n(Y) in M_n(A_P)`.
- `Phi_n(lambda_n(Y))_ij = Y_ij(e) = X_ij(g_i h_j) = L_ij`.
- By (J) for `M_n(A_P)` and Section 1.3,
  `Delta(lambda_n(Y)) >= Delta(L) = |det L|^(1/n)`.
- `lambda_n(X) = U lambda_n(Y) V` with `U = diag(lambda(g_i))` and
  `V = diag(lambda(h_j))` unitary, so `Delta(lambda_n(X)) = Delta(lambda_n(Y))`.
- If `det L != 0`, then `Delta(lambda_n(X)) > 0`. So `lambda_n(X)` is injective,
  hence has dense range (finite von Neumann algebra), and by (1.1), (1.2)
  `det_N(G)(r_X) = Delta(lambda_n(X))^n >= |det L|`.
- If `det L = 0` the displayed inequality is trivial.

For integral `X`, `det L` is a nonzero integer.

*The two special cases.*

- *Rows.* If `g_i` is the `<`-minimum of the support of row `i`, then every `h` in
  that support has `g_i^-1 h in P ∪ {e}`.
- *Columns.* If `h_j` is the `<'`-minimum of the support of column `j`, then every
  `h` there has `h h_j^-1 in P ∪ {e}`.

∎

*Proof of (c).* Let `A in M_(1 x n)(Z[G])`, so `r_A : l^2(G) -> l^2(G)^n`.

- If `A = 0`, then `det(r_A) = 1` by convention.
- Otherwise `A A^* = sum_j A_j A_j^*` lies in `Z[G]`, and its coefficient at `e`
  is `sum_j sum_g |A_j(g)|^2 > 0`, so `A A^* != 0`.
- By Section 1.1, `det(r_A)^2 = det(r_A^* r_A) = det(r_(A A^*)) >= 1` by (a).

For `A in M_(n x 1)(Z[G])`:

- `det(r_A) = det(r_A^*) = det(r_(A^*))`;
- `det(r_(A^*))^2 = det(r_(A^*)^* r_(A^*)) = det(r_A r_(A^*)) = det(r_(A^* A))`;
- `A^* A in Z[G]` is nonzero when `A != 0`, so (a) applies.

∎

*Proof of (d).*

- **No atoms.** For `r in R`, `x - r 1` is a nonzero element of `C[G]`, so by (a)
  `lambda(x) - r` is injective and `mu_x({r}) = 0`.
- **Serre inequalities.** Let `Q in Z[t]` be nonzero. Then `Q(x) in Z[G]`, and
  `|Q(lambda(x))| = |Q|(lambda(x))` by functional calculus, so

  ```text
  log Delta(lambda(Q(x))) = integral log |Q(t)| d mu_x(t).
  ```

  The integral is taken with `log 0 = -infinity`, and the zero set of `Q` is
  `mu_x`-null.
- If `Q(x) != 0` in `Z[G]`, then (a) gives `Delta(lambda(Q(x))) >= 1`.
- `Q(x) = 0` is impossible. `Q` splits over `C` as `c prod (t - r_i)`, so
  `prod (x - r_i) = 0` in `C[G]`. But `C[G]` has no zero divisors for
  left-orderable `G`, because of unique products. For finite nonempty `A`, `B`,
  the `<`-maximum of `AB` is `a^* b_max`, where `b_max = max B` and `a^*`
  maximizes `a b_max`. If `a' b' = a^* b_max`, then
  `a' b' <= a' b_max <= a^* b_max` forces `b' = b_max` and `a' = a^*`. So some
  `x - r_i = 0` and `x` would be a scalar. An integral scalar is in `Z 1`, which is
  excluded.

∎

**Remark 3.1 (relation to the Serre-class reformulation).** The graph claim
`determinant-conjecture-iff-serre-class-spectra` shows the conjecture for `G` is
equivalent to the Serre inequalities for all self-adjoint integral matrices
`A in M_n(Z[G])`. Theorem A(d) gives the case `n = 1`. For `n >= 2`, Theorem A(b)
gives it only for those `A` and `Q` with `L(Q(A))` nonsingular for some choice of
translations. That condition is not closed under polynomial functional calculus,
which is where this method stops.

## 4. Theorem B: invariant random orders

Keep the setting of Section 2 with an arbitrary countable group `Gamma`.

**Definition 4.1.** Let `S` be a finite nonempty subset of `Gamma`. An invariant
random order `mu` is *`S`-good* if for `mu`-a.e. `omega` the map

```text
beta  |->  min_omega(beta S),        Gamma -> Gamma,
```

is a bijection. By Section 5 it is equivalent to ask that the map be injective a.e.,
or surjective a.e., or that `N_S = 1` a.e. for the function `N_S` of (4.2).

For `S`-good `mu` and a.e. `omega`, let `kappa_S(omega)` be the unique `k in S` with
`min_omega(k^-1 S) = e`. Such `k` exists and is unique: `beta = k^-1` is the
unique `beta` with `min_omega(beta S) = e`, and `e in beta S` forces
`beta^-1 in S`.

**Theorem B.** Let `X in M_n(C[Gamma])` have nonzero rows, and let
`S_i = union_j supp X_ij` be the support of row `i`. Suppose `mu` is `S_i`-good for
every `i`. For a.e. `omega` define `L_omega in M_n(C)` by

```text
L_omega(i, j) = X_ij( kappa_(S_i)(omega) ).
```

Then

```text
Delta(lambda_n(X)) >= exp (1/n) integral log |det L_omega| d mu(omega).        (4.1)
```

Consequently:

- if `det L_omega != 0` for a.e. `omega`, then `lambda_n(X)` and `r_X` are injective
  and `det_N(Gamma)(r_X) >= exp integral log |det L_omega| d mu`;
- if moreover `X` is integral, `det_N(Gamma)(r_X) >= 1`;
- for `n = 1`, `x in C[Gamma]` nonzero with support `S`, and `mu` `S`-good,

  ```text
  Delta(lambda(x)) >= exp integral log |x(min_omega S)| d mu(omega),
  ```

  and `det_N(Gamma)(r_x) >= 1` for nonzero integral `x` with such a support.

For `mu = delta_<` with `<` left invariant, `kappa_S = min_< S` by (2.1), and
Theorem B is the row case of Theorem A(b).

*Proof.* **Step 1: a partial isometry.** Fix a finite nonempty `S`. For `k in S`
let `E_k = {omega : min_omega S = k}`, a Borel partition of `Omega`. Put

```text
V_S = sum_(k in S) u_(k^-1) 1_(E_k)    in M,
N_S = sum_(k in S) 1_(k^-1 E_k)        in L^infinity(mu).                (4.2)
```

Since the `E_k` are disjoint,

```text
V_S V_S^* = sum_k u_(k^-1) 1_(E_k) u_(k^-1)^* = sum_k alpha_(k^-1)(1_(E_k)) = N_S.
```

Note that `omega in k^-1 E_k` iff `min_(k omega) S = k` iff
`min_omega(k^-1 S) = e`, by (2.1). So

```text
N_S(omega) = #{ k in S : min_omega(k^-1 S) = e }.                         (4.3)
```

If `mu` is `S`-good, Lemma 5.1 below gives `N_S = 1` a.e. Then:

- `V_S V_S^* = 1`, so `V_S^*` is an isometry;
- `M` is finite, so `V_S` is unitary;
- the sets `k^-1 E_k`, `k in S`, partition `Omega` modulo null sets, and on
  `k^-1 E_k` we have `kappa_S = k`.

**Step 2: the rotated matrix lies in `M_n(A)`.** Let `V = diag(V_(S_1), ..., V_(S_n))`,
a unitary in `M_n(M)`. For each `i, j`,

```text
(V lambda_n(X))_ij = V_(S_i) lambda(X_ij)
                   = sum_(k in S_i) sum_(h in supp X_ij) X_ij(h) 1_(k^-1 E^i_k) u_(k^-1 h),
```

where `E^i_k = {min_omega S_i = k}`. Here we used
`u_(k^-1) 1_(E^i_k) = alpha_(k^-1)(1_(E^i_k)) u_(k^-1) = 1_(k^-1 E^i_k) u_(k^-1)`.

- If `omega in E^i_k`, then `k <=_omega h` for every `h in S_i`, so
  `e <=_(k^-1 omega) k^-1 h`.
- Thus `k^-1 E^i_k ⊆ S_(k^-1 h)`, each term lies in `A_0`, and
  `V lambda_n(X) in M_n(A)`.
- The terms with `k^-1 h = e`, that is `h = k`, give

  ```text
  E_n(V lambda_n(X))_ij = sum_(k in S_i) X_ij(k) 1_(k^-1 E^i_k).
  ```

- By Step 1, at a.e. `omega` exactly one indicator in row `i` is `1`, namely the one
  with `k = kappa_(S_i)(omega)`. Hence `E_n(V lambda_n(X))(omega) = L_omega`.

**Step 3: Jensen.** By Proposition 2.1, the amplification in Section 1.3 and (J),

```text
Delta(lambda_n(X)) = Delta(V lambda_n(X)) >= Delta(E_n(V lambda_n(X)))
                   = exp (1/n) integral log |det L_omega| d mu(omega).
```

The first equality holds because `V` is unitary, and the last is Section 1.3 for
`D = L^infinity(mu)`. This is (4.1).

**The consequences.**

- If `det L_omega != 0` a.e., then `log |det L_omega|` takes finitely many finite
  values, so the right side of (4.1) is positive. Hence `lambda_n(X)` is injective,
  and (1.1), (1.2) give the determinant bound.
- For integral `X`, `|det L_omega| >= 1` a.e.
- For `n = 1`, `integral log |x(kappa_S)| dmu = sum_k mu(k^-1 E_k) log |x(k)|`,
  and `mu(k^-1 E_k) = mu(E_k)` by invariance. This equals
  `integral log |x(min_omega S)| d mu`.

∎

**Remark 4.2 (what `L_omega` is).** In the matrix case the rows of `L_omega` are
read at different translates `kappa_(S_i)(omega)`, so they cannot in general be
aligned to a single minimum. For integral `X` the hypothesis is: for every tuple
`(k_1, ..., k_n)` with `mu(intersection_i {kappa_(S_i) = k_i}) > 0`, the integer
matrix `[X_ij(k_i)]` is nonsingular.

## 5. The bijection criterion and an obstruction

**Lemma 5.1.** Let `S` be finite nonempty and `N_S` as in (4.2). Then:

1. `integral N_S d mu = 1`, and `N_S` takes values in `{0, 1, ..., |S|}`.
2. For every `gamma in Gamma` and every `omega`,
   `N_S(gamma^-1 omega) = #{ beta in Gamma : min_omega(beta S) = gamma }`.
3. The following are equivalent:
   - (i) `N_S = 1` a.e.;
   - (ii) for a.e. `omega`, `beta -> min_omega(beta S)` is injective;
   - (iii) for a.e. `omega`, it is surjective;
   - (iv) for a.e. `omega`, it is bijective.

*Proof.*

**(1).** `integral N_S = sum_k mu(k^-1 E_k) = sum_k mu(E_k) = 1`.

**(2).** Apply (4.3) at `gamma^-1 omega`, using (2.1):

- `min_(gamma^-1 omega)(k^-1 S) = gamma^-1 min_omega(gamma k^-1 S)`.
- So `N_S(gamma^-1 omega) = #{k in S : min_omega(gamma k^-1 S) = gamma}`.
- Substitute `beta = gamma k^-1`. A `beta` with `min_omega(beta S) = gamma` has
  `gamma in beta S`, so `k = beta^-1 gamma in S`. The substitution is therefore a
  bijection onto `{beta : min_omega(beta S) = gamma}`.

**(3).**

- *(i) implies (iv).* Each of the countably many sets
  `{omega : N_S(gamma^-1 omega) = 1} = gamma {N_S = 1}` has full measure, so for
  a.e. `omega` every `gamma` has exactly one preimage, by (2).
- *(iv) implies (ii) and (iii)* trivially.
- *(ii) implies (i).* By (2) at `gamma = e`, `N_S <= 1` a.e. Since the mean is `1`,
  `N_S = 1` a.e.
- *(iii) implies (i).* Symmetrically, `N_S >= 1` a.e. and the mean is `1`.

∎

**Examples of failure.**

1. **Finite groups, `|S| >= 2`.** The `omega`-maximum `m` of `Gamma` is never
   `min_omega(beta S)`, since `beta S` has at least two elements. So the map is not
   surjective.
2. **Torsion in `S = {e, g}`.** Here
   `N_S(omega) = [e <_omega g] + [e <_omega g^-1]`.
   - If `g^2 = e`, then `N_S in {0, 2}`, so no invariant random order is
     `{e,g}`-good.
   - More generally, consider the map `beta -> min_omega{beta, beta g}`.
     - It is not injective iff some `beta` has `beta < beta g` and
       `beta < beta g^-1`, a local minimum along `n -> beta g^n`.
     - It is not surjective iff some `beta` is a local maximum there.
     - So by Lemma 5.1, `{e,g}`-goodness says a.e. `omega` is strictly monotone
       along every coset `beta <g>`.
   - A finite cycle has a maximum, so torsion `g` never admits a `{e,g}`-good
     order.
3. **The Bernoulli random order** (Austin, Example 4.1: i.i.d. uniform labels
   `omega_h`, and `g <_omega h` iff `omega_g < omega_h`). For `|S| >= 2` it is
   never `S`-good.
   - The sets `k^-1 S`, `k in S`, are distinct and all contain `e`.
   - With positive probability `omega_e` is the smallest label on their union, and
     then `N_S = |S| >= 2`.

**Proposition 5.2 (obstruction).** Suppose `mu` is `S`-good for every `S` with
`|S| <= 3`. Then for `mu`-a.e. `omega`, the set `P_omega = {g : e <_omega g}` is
the positive cone of a left-invariant order on `Gamma`. In particular `Gamma` is
left-orderable.

So beyond left-orderable groups, Theorem B necessarily works support by support.

*Proof.* Write `[.]` for indicators.

**Step 1 (`P ⊔ P^-1`).** For `g != e`, take `S = {e, g}`. Then (4.3) gives
`N_S = [e < g] + [e < g^-1]`.

- If `g = g^-1`, then `N_S` is never `1`.
- Otherwise `N_S = 1` a.e. says exactly one of `g`, `g^-1` lies in `P_omega`.
- Intersecting over the countably many `g`: for a.e. `omega`,
  `Gamma = P_omega ⊔ {e} ⊔ P_omega^-1`.

**Step 2 (`PP ⊆ P`).** Let `g, h` be such that `S = {e, g, gh}` has three elements,
that is `g != e`, `h != e` and `gh != e`. By (4.3),

```text
k = e  : min(S) = e                   iff  e < g   and e < gh,
k = g  : min{g^-1, e, h} = e          iff  e < g^-1 and e < h,
k = gh : min{(gh)^-1, h^-1, e} = e    iff  e < (gh)^-1 and e < h^-1.
```

Put `p = [e < g]`, `q = [e < h]`, `r = [e < gh]`. On the full-measure set of
Step 1,

```text
N_S = p r + (1 - p) q + (1 - r)(1 - q).
```

Checking the eight cases, `N_S = 0` exactly when `(p,q,r) = (1,1,0)` or `(0,0,1)`,
and `N_S = 1` otherwise.

- So `N_S = 1` a.e. excludes `e < g, e < h, gh < e`.
- The cases `g = e`, `h = e` and `gh = e` are trivial or excluded by Step 1.
- Intersecting over all pairs: for a.e. `omega`, `P_omega P_omega ⊆ P_omega`.

A subset `P` with `Gamma = P ⊔ {e} ⊔ P^-1` and `PP ⊆ P` is the positive cone of the
left-invariant order `a < b iff a^-1 b in P`. ∎

**Remark 5.3.** The proof shows more. The single support `{e, g, gh}` together
with `{e,g}`, `{e,h}`, `{e,gh}` already forces the cone condition for that pair.
So for a non-left-orderable group and every invariant random order, some support
of size at most three is not good. The example of Section 7 shows that specific
supports can still be good.

## 6. Remarks and extensions

**6.1 Sanity check on `Z^d`.** For `G = Z^d` with a lexicographic order,
`Delta(lambda(x))` is the Mahler measure of `x` as a Laurent polynomial. Theorem A(a)
says the Mahler measure is at least the absolute value of the coefficient at a
lex-extreme exponent, the classical lower bound. For example, `x = 1 + 2t` on `Z`
has Mahler measure `2`, which is at least both extreme coefficients `1` and `2`.
In Theorem A(b), the lex-minimal monomial of `det X(z)` has coefficient `det L`
when `det L != 0`, so (b) reduces to the same bound for `det X(z)`.

**6.2 Elementary operations (standard, not used in the claims).** The
Fuglede--Kadison determinant is multiplicative: Fuglede--Kadison 1952; Lück,
*L^2-Invariants* (2002), Theorem 3.14 for weak isomorphisms; neither re-read in this
session. Also `Delta(1 + N) = 1` for strictly triangular `N` in `M_n(L(G))`: apply
(J) for the upper-triangular subdiagonal algebra of `M_n(L(G))`, with diagonal
expectation, to `1 + N` and `1 - N` and multiply. So Theorem A(b) extends to
`E_1 X E_2` with `X` as in (b) and `E_1`, `E_2` products of elementary matrices
`1 + r e_ij` over `Z[G]` and monomial matrices with entries `+-g`. We did not use
this, and the claims do not assert it.

**6.3 Groups not known to be sofic.** Theorem A applies to every left-orderable
group. In the graph:

- Thompson's group `F` is bi-orderable (`thompson-f-is-bi-orderable`), and both
  `thompson-f-is-sofic` and `thompson-f-is-not-sofic` are open;
- the Lodha--Moore group is bi-orderable and not LEA
  (`lodha-moore-group-is-bi-orderable-and-not-lea`);
- the soficity of the Lodha--Moore group is open (`lodha-moore-group-is-not-sofic`).

For these groups the determinant conjecture was not known (Elek--Szabó needs
soficity). Theorem A proves it for:

- all `1 x 1`, `1 x n` and `n x 1` integral matrices;
- all square integral matrices with a nonsingular leading-coefficient matrix for
  some choice of translations `g_i`, `h_j`.

It also gives the Serre inequalities, and atomlessness, for all self-adjoint
integral elements outside `Z 1`.

**6.4 Consequence for the refutation side.** Let `A` be an integral matrix
over a left-orderable group with `det_N(G)(r_A) < 1`. Then:

- `A` has at least two rows and at least two columns;
- `A A^*` and `A^* A`, and `A` itself if it is square, have singular
  leading-coefficient matrices `L` for every choice of translations `g_i`, `h_j`
  allowed in Theorem A(b). This uses
  `det(r_A)^2 = det(r_(A A^*)) = det(r_(A^* A))`.

Theorem B imposes the analogous condition for every invariant random order that is
good for the row supports. A left-orderable nonsofic host (the graph's open
`left-orderable-non-sofic-group`) therefore does not by itself help to refute the
conjecture with small matrices.

**6.5 Analytic zero divisors.** Theorem A(a) shows that for left-orderable `G` and
nonzero `x in C[G]`, `lambda(x)` and `r_x` are injective on `l^2(G)`. That is the
analytic zero-divisor conjecture for left-orderable groups. For locally indicable
groups it is expected to follow from the strong Atiyah conjecture results of
Jaikin-Zapirain--López-Álvarez (Math. Ann. 2020; *unverified*, not read in this
session). Left-orderable groups need not be locally indicable, for example
finitely generated perfect left-orderable groups (Bergman, Pacific J. Math. 147
(1991); *unverified*). We have not found this
consequence stated in the sources we read. It may nevertheless be known.

**6.6 Lopsided elements.** For `x = c(1 - y)` with `y in C[G]`,
`sum |y(g)| < 1` and `supp y ⊆ P`, the equality `Delta(lambda(x)) = |c|` follows
from the power series `log(1 - y) = - sum y^m / m`, since `tau(y^m) = 0`. This is
the invertible case of Jensen's formula and needs no Labuschagne input. Austin cites
Hayes, *Harmonic models and Bernoullicity*, for "lopsided" elements over ordered
groups; Hayes's paper was not read here. Theorem A needs the full inequality (J)
precisely for non-invertible, non-lopsided elements such as `1 + a + b` in `F_2`.

**6.7 Austin's Problem 4.7.** Austin (arXiv:2412.13751v4, Section 4.4) asks:
"Does the construction of a subdiagonal subalgebra from an invariant random order
shed any light on these open questions about L2-invariants?" The open questions
named there include Lück's approximation and determinant conjectures. Theorem B and
Proposition 5.2 give a partial answer.

- **Yes, support by support.** The random-order subdiagonal algebra proves the
  determinant conjecture for integral matrices whose row supports are good for some
  invariant random order, with nonsingular `L_omega`.
- **Not uniformly.** An invariant random order good for all supports of size at most
  three exists only on left-orderable groups, where the deterministic Arveson
  algebra already suffices.

## 7. A non-left-orderable example

<!-- SECTION 7 -->

## 8. What is new, and the sources checked

<!-- SECTION 8 -->

## 9. Attempts that failed

<!-- SECTION 9 -->
