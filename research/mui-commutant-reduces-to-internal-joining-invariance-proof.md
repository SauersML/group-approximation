---
rg: 2
id: mui-commutant-reduces-to-internal-joining-invariance-proof
kind: route
title: Take entrywise positive parts to turn MUI vectors into internal measures, then test the external joining shadow on Bernoulli shifts over genuine finite quotients
target: mui-commutant-reduces-to-internal-joining-invariance
requires:
  - planted-lifts-defeat-hilbert-level-gaussian-soficity
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Notation is that of the claim. Write `Y = Y_n`, `W = Y × Y`, and
`<xi, eta>_n = |Y|^(-1) sum_(w in W) xi(w) conj(eta(w))`. The operator
`psi_n(g)` acts on functions on `W` by `(psi_n(g) xi)(w) = xi(psi_n(g)^(-1) w)`,
a permutation of coordinates. Limits are along `U`.

## Step 1: entrywise calculus

**Lemma 1.1.** Let `F : C -> R` be `L`-Lipschitz with `F(0) = 0`. For
`xi = [xi_n] in H` put `F(xi) = [F o xi_n]`. Then:

- (i) `F(xi)` is well defined and `||F(xi) - F(eta)|| <= L ||xi - eta||`;
- (ii) `psi_n(g) (F o xi_n) = F o (psi_n(g) xi_n)` for every `g` and `n`;
- (iii) if `xi` is MUI, then so is `F(xi)`;
- (iv) if `xi in H^eq(s)`, then `F(xi) in H^eq(s)`; if `xi` is
  `Gamma`-invariant, then so is `F(xi)`.

*Proof.* (i): `|F(z) - F(z')| <= L|z - z'|` pointwise, and
`|F(z)| <= L|z|` gives bounded norms. (ii): `psi_n(g)` permutes the
coordinates, and `F` acts coordinatewise. (iii): the row masses of `F(xi)`
are at most `L^2` times those of `xi`, and uniform integrability passes to
dominated families. (iv): by (ii) and (i),
`||psi(gh)F(xi) - psi(g)psi(h)F(xi)|| = ||F(psi(gh)xi) - F(psi(g)psi(h)xi)||
<= L ||psi(gh)xi - psi(g)psi(h)xi|| = 0`, and in the same way for
`||psi(gamma)F(xi) - F(xi)||`. ∎

Apply this to `F_1 = (Re)_+`, `F_2 = (Re)_-`, `F_3 = (Im)_+`, `F_4 = (Im)_-`
(all `1`-Lipschitz, vanishing at `0`). Then
`xi = F_1(xi) - F_2(xi) + i F_3(xi) - i F_4(xi)` exactly, at every `n`.

**Corollary 1.2.** (MUI-C) holds if and only if it holds for nonnegative
vectors. Indeed, if each `F_j(xi)` is `N`-invariant then so is `xi`, and by
Lemma 1.1 each `F_j(xi)` is a nonnegative `Gamma`-invariant vector of
`H^eq_MUI`. ∎

## Step 2: nonnegative vectors are internal measures

Let `xi >= 0` in `H` with `||xi|| = c > 0`. Put
`lambda_n = xi_n^2 / (|Y| ||xi_n||_n^2)`, a probability measure on `W`
(defined for `U`-almost every `n`). Conversely, an internal pair measure
`lambda` gives the nonnegative unit vector `xi_n = (|Y| lambda_n)^(1/2)`.
These are inverse bijections between nonnegative vectors of norm `c` and
internal measures, up to the scalar `c`.

**Lemma 2.1 (dictionary).** For nonnegative `xi, eta` of norm `1` with
measures `lambda, kappa`:

- (i) `||xi_n - eta_n||_n^2 = sum_w (lambda_n(w)^(1/2) - kappa_n(w)^(1/2))^2
  = 2 h_n^2`, where `h_n` is the Hellinger distance, and
  `h_n^2 <= ||lambda_n - kappa_n||_TV <= 2^(1/2) h_n`
  (TV normalized as `sup_A |lambda_n(A) - kappa_n(A)|`);
- (ii) `psi_n(g) xi_n` is the vector of `psi_n(g)_* lambda_n`;
- (iii) the row mass of `xi_n` at `a` is `|Y| (p_1)_* lambda_n (a)`. So `xi`
  is MUI iff `lambda` is MUI, in the sense of the claim.

*Proof.* (i) is the definition of Hellinger distance with the standard
inequalities `h^2 <= TV <= sqrt 2 h`. (ii): `psi_n(g)` is a permutation of
`W`, and it commutes with squaring. (iii) is immediate from the definition
of row mass and `||xi_n|| = 1`. ∎

Hence `xi` is `Gamma`-invariant (resp. `N`-invariant, resp. in `H^eq`) iff
`lambda` is internally `Gamma`-invariant (resp. internally `N`-invariant,
resp. internally equivariant). Combined with Corollary 1.2 this proves
**Theorem (1)**: (MUI-C) ⟺ (MUI-J). ∎

**Remark 2.2 (why this leaves L^2(M)).** The positive part of a bounded
matrix need not be bounded. For the Fourier unitary
`x_n(a,b) = |Y|^(-1/2) exp(2 pi i ab/|Y|)`, the entrywise modulus is
`J/|Y|^(1/2)`, of operator norm `|Y|^(1/2)`, and its singular values are not
uniformly integrable, so it does not lie in `L^2(M)`. This is why the
natural space for the reduction is `H^eq_MUI`, and CCR does not reduce to
nonnegative matrices inside `M`.

## Step 3: standard parts

Let `X = (Loeb(Y_n), mu_X)`. For internal sets `A = [A_n], B = [B_n]` of
`Y_n` put `st(lambda)(A × B) = lim lambda_n(A_n × B_n)`. The marginals are
the standard parts of `(p_i)_* lambda_n`. If `lambda` is MUI, then
`lim lambda_n(A_n × Y_n) -> 0` as `mu_X(A) -> 0` uniformly, so the marginal
premeasures are absolutely continuous with respect to `mu_X`, and the
premeasure on rectangles extends (Carathéodory, as in the Loeb construction)
to a finite measure on the product sigma-algebra `B_X ⊗ B_X`. If `lambda` is
internally `g`-invariant, then
`st(lambda)((gA) × (gB)) = lim lambda_n(psi_n(g)(A_n × B_n))`
`= lim (psi_n(g)^(-1)_* lambda_n)(A_n × B_n) = lim lambda_n(A_n × B_n)`
`= st(lambda)(A × B)`, the third equality by internal invariance, so
`st(lambda)` is `g`-invariant for the Loeb action. (The Loeb action of `g` is
induced by `s_n(g)`; it is a measure-preserving action of `G`, since `sigma`
is a homomorphism modulo Hamming-null sequences.)

## Step 4: the genuine Bernoulli models (Theorem (2))

`G` is residually finite (Kun--Thom Theorem E) and countable, so there are
surjections `pi_n : G -> Q_n` onto finite groups with
`ker pi_(n+1) ⊆ ker pi_n` and `∩ ker pi_n = {e}`. Let `K = {0,1}`,
`Y_n = K^(Q_n)`, and `(s_n(g) a)(q) = a(pi_n(g)^(-1) q)`. Each `s_n` is an
exact homomorphism `G -> Sym(Y_n)`.

**Lemma 4.1.** `sigma = [s_n]` is an injective trace-faithful sofic
representation.

*Proof.* Let `g != e`. For large `n`, `pi_n(g)` has order `o >= 2`, and left
multiplication by it has `|Q_n|/o <= |Q_n|/2` cycles on `Q_n`. A point `a` is
fixed by `s_n(g)` iff it is constant on these cycles. So the fixed fraction is
`|K|^(|Q_n|/o - |Q_n|) <= 2^(-|Q_n|/2) -> 0`. ∎

**Lemma 4.2 (finite collapse).** `pi_n(N) = pi_n(Gamma)` for every `n`.

*Proof.* For `t` in the compression semigroup `P_Gamma`,
`pi_n(t) pi_n(Gamma) pi_n(t)^(-1) = pi_n(t Gamma t^(-1)) ⊆ pi_n(Gamma)`, and both
sides have the same finite cardinality, so they are equal. Hence `pi_n(t)`
and `pi_n(t)^(-1)` normalize `pi_n(Gamma)`. Since `P_Gamma` generates `G`,
`pi_n(Gamma)` is normal in `Q_n`, and so contains the normal closure
`pi_n(N)` of `pi_n(Gamma)`. The reverse inclusion is `Gamma ⊆ N`. ∎

**Proof of (2a).** Let `(S, kappa)` be a Kazhdan pair for `Gamma`. Let
`xi in H` be `Gamma`-invariant, and put
`eps_n = max_(s in S) ||psi_n(s) xi_n - xi_n||_n`, so `eps_n -> 0`. The map
`psi_n` restricted to `Gamma` is a genuine unitary representation on
`l^2(W_n)`. Let `P_n` be the projection onto its invariant vectors. Then
`||xi_n - P_n xi_n|| <= eps_n / kappa`: the vector `xi_n - P_n xi_n` is
orthogonal to the invariants, and `P_n` commutes with `psi_n(Gamma)`. Since
`psi_n` factors through `Q_n`, Lemma 4.2 gives `psi_n(u) in psi_n(Gamma)` for
every `u in N`, so `psi_n(u) P_n xi_n = P_n xi_n` and
`||psi_n(u) xi_n - xi_n|| <= 2 eps_n / kappa -> 0`. No MUI hypothesis was
used. (MUI-J) follows through Step 2. ∎

**Proof of (2b).** For `h in G` let `f_h = [f_(h,n)]`,
`f_(h,n)(a) = a(pi_n(h))`. For distinct `h_1, ..., h_k`, eventually the
`pi_n(h_i)` are distinct, and then `f_(h_1,n), ..., f_(h_k,n)` are exactly
i.i.d. uniform on `K` under the uniform measure of `Y_n`. So in `X` the
`f_h` are i.i.d. uniform. Moreover
`f_(h,n)(s_n(g)^(-1) a) = a(pi_n(gh)) = f_(gh,n)(a)`, so `g · f_h = f_(gh)`,
where `(g · f)(x) = f(g^(-1) x)`. Thus `B = sigma(f_h : h in G)` is a
`G`-invariant factor isomorphic to the Bernoulli shift `K^G`, and for
`S ⊆ G` the sigma-algebra `F_S = sigma(f_h : h in S)` satisfies
`g · F_S = F_(gS)`. In particular `F_Gamma` is `Gamma`-invariant.

Let `lambda_Gamma` be the relatively independent self-joining of `X` over
`F_Gamma`:
`int f(x) g(y) d lambda_Gamma = int E(f|F_Gamma) E(g|F_Gamma) d mu_X`.
Its marginals are `mu_X`. Since `gamma` preserves `mu_X` and `F_Gamma`,
conditional expectation onto `F_Gamma` commutes with `gamma`, so
`lambda_Gamma` is `Gamma`-invariant.

For `h in Gamma`, `f_h` is `F_Gamma`-measurable, so
`lambda_Gamma(f_h(x) = f_h(y)) = 1`. For `h notin Gamma`, `f_h` is independent of
`F_Gamma` (independence is a property of the joint law, and the `f_h` are
independent), so `E(1_(f_h = k) | F_Gamma) = 1/2` and
`lambda_Gamma(f_h(x) = f_h(y)) = sum_k 1/4 = 1/2`. Since `Gamma` is not
normal, `N ⊋ Gamma`; take `u in N \ Gamma`. Then
`((u × u)_* lambda_Gamma)(f_u(x) = f_u(y)) = lambda_Gamma(f_e(x) = f_e(y)) = 1`,
while `lambda_Gamma(f_u(x) = f_u(y)) = 1/2`. So `lambda_Gamma` is not
`u`-invariant. ∎

**Proof of (2c).** Suppose `lambda` is an MUI internally `Gamma`-invariant
internal pair measure with `st(lambda) = lambda_Gamma`. Since each `s_n` is a
homomorphism, `lambda` is internally equivariant. By (2a) and Step 2,
`lambda` is internally `N`-invariant, and by Step 3 `st(lambda)` is
`N`-invariant, contradicting (2b). For the operator: `E = E(·|F_Gamma)` on
`L^2(X)` is a self-adjoint Markov projection with `gamma E gamma^(-1) = E`
for `gamma in Gamma`, while `u E u^(-1) = E(·|F_(uGamma)) != E`, because
`f_u` is `F_(uGamma)`-measurable and independent of `F_Gamma`. ∎

## Step 5: why the listed arguments die

Each listed argument, applied to the Bernoulli model of Step 4, would take the
input "`Gamma`-invariant self-joining (resp. `Gamma`-invariant factor, resp.
`Gamma`-equivariant Markov operator) of the sofic `G`-action `X`" and
conclude `N`-invariance. Step 4 supplies such an input (`lambda_Gamma`,
`F_Gamma`, `E`) whose conclusion is false, and `X` is the Loeb space of an
exact, coordinatewise genuine sofic representation, which is the most
favourable case (there (MUI-C) holds by (2a)). So any correct argument for
(MUI-J) must use a property of internal measures that `lambda_Gamma` fails to
have. By (2c) that property is internal TV-invariance itself, as opposed to
invariance of the standard part.

**Relation to the planted obstruction.** The planted lifts show that
`Gamma`-invariance in `H^eq` without MUI allows enemy dynamics. Here the
measure is MUI (its marginals are exactly `mu_X`), `Gamma`-invariant and not
`N`-invariant. But it exists only externally. The two obstructions together
say: marginal control and exact internal invariance are both needed, and
neither suffices when separated from the other.
