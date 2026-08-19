# Approximate normalizers of a full diagonal masa are monomial

Date: 2026-08-14

## 0. What this note settles

Kun--Thom, arXiv:2608.06222, Definition 2.2 (following Paunescu,
arXiv:1002.0605, Definition 1.4) calls a p.m.p. action `G` on `(X,mu)`
*sofic* when there are finite sets `Y_n` and a trace-preserving embedding

```text
Theta: L^infty(X) crossed_product G -> product_(n->U) M_(|Y_n|)(C)   (DNR1)
```

with `Theta(L^infty(X)) subset D_U` and `Theta(u_g) in S_U`, where `D_U` is
the diagonal ultraproduct and `S_U=product_(n->U) Sym(Y_n)` is the universal
sofic group.  Their Corollary D says the generalized Bernoulli action of an
infranormal nonnormal Kazhdan pair is *not* sofic in this sense.

Connes embeddability of the same crossed product asks only for an embedding
of type `(DNR1)` with **no** constraint on where `Theta(L^infty(X))` and
`Theta(u_g)` land.  This note fixes exactly how much of the gap between the
two statements is real:

1. the constraint `Theta(L^infty(X)) subset D_U` is **free** — it can always
   be arranged (Lemma 2, already recorded in `notes/NOTEPAD.md`);
2. the constraint `Theta(u_g) in S_U` can be weakened all the way to
   `Theta(u_g) in N(D_U)` — the unitary normalizer — **without weakening the
   notion at all** (Theorem 6).  The engine is a quantitative rigidity
   statement for approximate normalizers of a *full* masa (Lemma 3);
3. consequently the *only* surviving freedom is that the group unitaries
   need not normalize the ambient diagonal.  All exoticity is stored in the
   multiplicity fibers, and the Fourier-block example of Section 7 shows the
   fibers really do carry it.

A consequence for route selection is drawn in
`notes/FALSE_MASA_NORMALIZING_TRACIAL_ACTION.md`: the "tracial `C`-action"
obtained by replacing `Sym(A)` in Alekseev--Bradford Definition 4.23 with a
masa-normalizing map into `U(n)` is **not** a weakening of a sofic action.

Throughout, `tr` is the normalized trace on `M_N(C)`,
`||x||_2 = tr(x^* x)^(1/2)` the normalized Hilbert--Schmidt norm, `D_N` the
diagonal masa, and `E_N: M_N -> D_N` the trace-preserving conditional
expectation (retain the diagonal entries).  `U` is a fixed nonprincipal
ultrafilter.

## 1. The exact finite-level normalizer

**Fact 1.**  `N_(U(N))(D_N)` is the group of *monomial* unitaries, i.e.
`P_sigma d` with `sigma in Sym(N)` a permutation matrix and `d` a diagonal
unitary.

This is standard: a unitary normalizing `D_N` permutes its `N` minimal
projections, and a unitary carrying `e_j` to `e_(sigma(j))` for all `j` maps
each coordinate line onto a coordinate line.

## 2. Abelian subalgebras are free to diagonalize

**Lemma 2 (abelian diagonalization).**  Let `A` be a separable abelian
finite von Neumann algebra and `Theta: A -> product_(n->U) M_(d_n)(C)` a
trace-preserving `*`-homomorphism.  There is a unitary `v` in the
ultraproduct with `v Theta(A) v^* subset product_(n->U) D_(d_n)`.

*Proof.*  A separable abelian von Neumann algebra has a single self-adjoint
generator `a`.  Lift the self-adjoint `Theta(a)` to uniformly bounded
self-adjoint `a_n in M_(d_n)`, diagonalize `a_n = v_n^* lambda_n v_n` with
`lambda_n` diagonal, and set `v=(v_n)_U`.  Trace preservation makes `Theta`
normal, so `Theta(A)=W^*(Theta(a))`, and `W^*((lambda_n)_U)` is contained in
the diagonal ultraproduct, which is a von Neumann subalgebra.  End proof.

(This lemma is already in `notes/NOTEPAD.md`; it is restated because
Theorem 6 uses it.)

Note the scope: Lemma 2 diagonalizes the *abelian* part only.  It says
nothing about the unitaries implementing an action on it.

## 3. The rigidity lemma

For `u in U(N)` put

```text
def_D(u) = sup{ ||u f u^* - E_N(u f u^*)||_2 : f=f^* in D_N, ||f||<=1 }. (DNR2)
```

`def_D(u)=0` iff `u` normalizes `D_N`.

**Lemma 3 (approximate normalizers of a full masa are monomial).**  Let
`u in U(N)` with `def_D(u) <= delta <= 1`.  Then there is a monomial unitary
`w in N_(U(N))(D_N)` with

```text
||u-w||_2 <= 3 sqrt(delta).                                   (DNR3)
```

*Proof.*  Let `A` be the `N x N` matrix `A_(ij) = |u_(ij)|^2`.  Since `u` is
unitary, `A` is doubly stochastic.  For real diagonal `f=diag(f_1,...,f_N)`,

```text
(E_N(u f u^*))_(ii) = sum_j |u_(ij)|^2 f_j = (Af)_i,
```

`||u f u^*||_2 = ||f||_2`, and `E_N` is the `||.||_2`-orthogonal projection
onto `D_N`, so by Pythagoras

```text
||u f u^* - E_N(u f u^*)||_2^2 = ||f||_2^2 - ||Af||_2^2,      (DNR4)
```

with `||.||_2` the normalized Euclidean norm on `C^N` on the right.

Now average `(DNR4)` over uniform random signs `f=epsilon in {-1,1}^N`,
each of which is a self-adjoint contraction in `D_N`.  Then
`||epsilon||_2^2 = 1` and

```text
E_epsilon ||A epsilon||_2^2
   = (1/N) sum_i E_epsilon ( sum_j A_(ij) epsilon_j )^2
   = (1/N) sum_i sum_j A_(ij)^2.
```

Since some sign vector attains at least the average of
`1 - ||A epsilon||_2^2`, hypothesis `(DNR2)` gives

```text
(1/N) sum_i ( sum_j A_(ij)^2 ) >= 1 - delta^2.                 (DNR5)
```

Each row of `A` is a probability vector, so
`sum_j A_(ij)^2 <= max_j A_(ij) <= 1`.  Hence `(DNR5)` reads
`E_i [ 1 - max_j A_(ij) ] <= delta^2`, and Markov's inequality gives a set
`Good` of at least `(1-delta)N` indices with

```text
max_j A_(ij) >= 1 - delta   for i in Good.                      (DNR6)
```

For `i in Good` let `pi(i)` be a maximizing column.  Because the columns of
`A` also sum to `1`,

```text
sum_(i in Good) A_(i,pi(i)) >= (1-delta)^2 N >= (1-2delta)N,
```

while for any fixed column `j` the total mass `sum_i A_(ij)` is `1`; hence
at most `2 delta N` indices of `Good` can be discarded to make `pi`
injective.  Let `Good_0 subset Good` be the resulting set,
`|Good_0| >= (1-3delta)N`, with `pi` injective on it, and extend `pi` to a
permutation `sigma in Sym(N)`.  Define the monomial unitary `w` by

```text
w_(i,sigma(i)) = u_(i,pi(i))/|u_(i,pi(i))|   for i in Good_0,
w_(i,sigma(i)) = 1                            otherwise,
```

all other entries zero.  For `i in Good_0`,

```text
sum_(j != pi(i)) |u_(ij)|^2 <= delta,
| |u_(i,pi(i))| - 1 |^2 <= (1-sqrt(1-delta))^2 <= delta^2,
```

so that row contributes at most `delta + delta^2` to
`N ||u-w||_2^2`; each of the at most `3 delta N` remaining rows contributes
at most `2`.  Hence

```text
||u-w||_2^2 <= delta + delta^2 + 6 delta <= 8 delta,
```

which gives `(DNR3)`.  End proof.

The constant is not optimized; only `||u-w||_2 -> 0` as `delta -> 0`,
uniformly in `N`, is used below.

**Lemma 4 (ultraproduct form).**  Let `u` be a unitary of
`product_(n->U) M_(d_n)` with `u D_U u^* subset D_U`.  Then
`u in S_U . U(D_U)`, and this factorization is unique.  Consequently

```text
N(D_U) = S_U semidirect U(D_U).                                 (DNR7)
```

*Proof.*  Lift `u` to unitaries `u_n in U(d_n)` and put
`delta_n = def_(D_(d_n))(u_n)`; the supremum in `(DNR2)` is attained by
compactness, so choose maximizers `f_n`.  If `lim_U delta_n = 3c > 0` then
`f=(f_n)_U` is a self-adjoint contraction in `D_U` with `u f u^* in D_U`,
i.e. there are diagonal `g_n` with `lim_U ||u_n f_n u_n^* - g_n||_2 = 0`;
since `E_n` is the nearest-point projection onto `D_(d_n)`,

```text
delta_n = ||u_n f_n u_n^* - E_n(u_n f_n u_n^*)||_2
        <= ||u_n f_n u_n^* - g_n||_2 ->_U 0,
```

a contradiction.  So `lim_U delta_n = 0`, and Lemma 3 supplies monomial
`w_n = P_(sigma_n) d_n'` with `lim_U ||u_n - w_n||_2 = 0`.  Then
`u = (P_(sigma_n))_U . (d_n')_U in S_U . U(D_U)`.

For uniqueness, if `s d = s' d'` with `s,s' in S_U` and `d,d' in U(D_U)`
then `(s')^(-1) s in S_U cap U(D_U)`.  A permutation matrix
`||.||_2`-close to a diagonal matrix must be close to the identity
permutation: `||P_sigma - e||_2^2 = 2 d_H(sigma, id)` where `d_H` is the
normalized Hamming distance, and the nearest diagonal to `P_sigma` is
supported on the fixed points of `sigma`.  Hence
`S_U cap U(D_U) = {1}` and the factorization is unique.  Permutations
normalize `U(D_U)`, giving `(DNR7)`.  End proof.

**Lemma 5 (multiplicativity transfer).**  Let `F` be a finite subset of a
group `Gamma` and `phi: Gamma -> U(N)` with `def_D(phi(g)) <= delta` for
`g in F` and `||phi(g)phi(h) - phi(gh)||_2 < epsilon` whenever
`g,h,gh in F`.  Write `phi(g) = w_g + r_g` with `w_g = P_(pi(g)) d_g`
monomial and `||r_g||_2 <= 3 sqrt(delta)` (Lemma 3).  Then

```text
d_H( pi(g) pi(h), pi(gh) ) <= ( epsilon + 9 sqrt(delta) )^2 / 2. (DNR8)
```

*Proof.*  `||w_g w_h - w_(gh)||_2 <= epsilon + 3.(3 sqrt(delta))` by the
triangle inequality and unitarity.  Both `w_g w_h` and `w_(gh)` are monomial,
with underlying permutations `pi(g)pi(h)` and `pi(gh)`.  Two monomial
unitaries whose permutations disagree at a column contribute `2` to
`N ||.||_2^2` at that column, so
`||P_sigma a - P_tau b||_2^2 >= 2 d_H(sigma,tau)` for any diagonal unitaries
`a,b`.  End proof.

Lemmas 3 and 5 together say: *a normalized-Hilbert--Schmidt almost
representation that almost normalizes a full diagonal masa is a Hamming
almost representation by permutations, with a comparable defect.*

## 4. Normalizer-Cartan embeddings are already Paunescu-sofic

**Theorem 6.**  Let `G` be a countable sofic group acting p.m.p. on
`(X,mu)` with `X` standard.  Suppose there are finite sets `Y_n` and a
trace-preserving embedding `Theta` as in `(DNR1)` such that

```text
Theta(L^infty(X)) subset D_U    and    Theta(u_g) in N(D_U) for all g. (DNR9)
```

Then the action is sofic in the sense of Kun--Thom Definition 2.2.

*Proof.*  By Lemma 4 write `Theta(u_g) = s_g c_g` uniquely with `s_g in S_U`
and `c_g in U(D_U)`.

*`s` is a homomorphism.*  From `Theta(u_g)Theta(u_h)=Theta(u_(gh))`,

```text
s_g c_g s_h c_h = s_g s_h ( s_h^(-1) c_g s_h ) c_h = (s_g s_h) c'
```

with `c' in U(D_U)` because `S_U` normalizes `U(D_U)`.  Uniqueness of the
factorization of `Theta(u_(gh))` gives `s_g s_h = s_(gh)`.

*`s` implements the action.*  For `f in L^infty(X)`, `Theta(f) in D_U` and
`c_g in U(D_U)` commute, since `D_U` is abelian.  Hence

```text
s_g Theta(f) s_g^* = s_g c_g Theta(f) c_g^* s_g^*
                   = Theta(u_g) Theta(f) Theta(u_g)^*
                   = Theta(alpha_g(f)).                        (DNR10)
```

*Amplification removes the residual trace defect.*  Nothing so far forces
`tr(s_g)=0`, so `s` need not be a sofic representation and
`f u_g |-> Theta(f) s_g` need not be trace preserving.  Fix this with an
independent free sofic representation.  Since `G` is sofic there are finite
sets `Y'_n` and a homomorphism `sigma: G -> product_(n->U) Sym(Y'_n)` with
`tr(sigma(g))=0` for `g != 1`.  Work on `Y_n x Y'_n` and put

```text
s^_g = s_g (x) sigma_g in Sym(Y_n x Y'_n),
Theta^(f u_g) = ( Theta(f) (x) 1 ) . s^_g.                      (DNR11)
```

`g |-> s^_g` is a homomorphism into `S^_U = product_(n->U) Sym(Y_n x Y'_n)`
(the Hamming metric on a product is dominated coordinatewise), and
`Theta(f) (x) 1` lies in the diagonal ultraproduct of `M_(|Y_n||Y'_n|)`.
By `(DNR10)`, `s^_g` implements `alpha_g` on `Theta(L^infty(X)) (x) 1`, so
`Theta^` is a `*`-homomorphism on the algebraic crossed product.  Its trace
is

```text
tr( (Theta(f) (x) 1) (s_g (x) sigma_g) ) = tr(Theta(f) s_g) . tr(sigma_g),
```

which vanishes for `g != 1` and equals `integral f dmu` for `g=1`.  So
`Theta^` is trace preserving on the algebraic crossed product, hence extends
to a normal trace-preserving (thus injective) embedding of
`L^infty(X) crossed_product G`.  It satisfies both requirements of
Definition 2.2.  End proof.

**Corollary 7.**  Let `Gamma<G` be an infranormal nonnormal Kazhdan pair
with `G` residually finite (Kun--Thom Theorem E supplies one), let
`Y=G/Gamma` and

```text
M_KT = L^infty({-1,1}^Y) crossed_product G
     = L( (directSum_Y C_2) semidirect G ) = L(W).             (DNR12)
```

Then **no** trace-preserving embedding of `M_KT` into a matrix tracial
ultraproduct satisfies `(DNR9)`.

*Proof.*  Kun--Thom Corollary D says the generalized Bernoulli action
`G` on `({-1,1},kappa)^(G/Gamma)` is not sofic; apply Theorem 6.  End proof.

**Corollary 8 (the exact remaining freedom).**  `W` is hyperlinear iff there
is a trace-preserving embedding `Theta: M_KT -> product_U M_(d_n)` with
`Theta(L^infty({-1,1}^Y)) subset D_U` for which some `Theta(u_g)` fails to
normalize `D_U`.

*Proof.*  `W` is hyperlinear iff `M_KT` is Connes embeddable (Pestov,
*Hyperlinear and sofic groups: a brief guide*, Theorem 8.5), iff `M_KT`
embeds trace preservingly into some `product_U M_(d_n)`.  Given any such
embedding, Lemma 2 conjugates the Bernoulli algebra into `D_U`; Corollary 7
then forbids all `Theta(u_g)` from normalizing `D_U`.  End proof.

So the *Cartan* half of Definition 2.2 is vacuous and the *permutation* half
is equivalent to the strictly weaker-looking *normalizer* half.  The entire
distance between "sofic action" and "Connes embeddable crossed product" is
the single question of whether the ambient masa can be chosen invariantly.

## 5. The naive Hilbert--Schmidt relaxation collapses

**Theorem 9.**  Call `phi: Gamma -> U(N)` a *masa-normalizing tracial model*
of an action if it is `(F,epsilon)`-multiplicative in `||.||_2` and
`def_D(phi(g)) <= delta` for `g in F`, and the transported lamp data are
carried correctly.  Then by Lemmas 3 and 5 the permutations `pi(g)` are
`((epsilon+9 sqrt delta)^2/2)`-multiplicative in the Hamming metric, and the
lamp covariance transfers to them because `||phi(g)-w_g||_2 <= 3 sqrt delta`.
Hence every masa-normalizing tracial model contains a permutation model of
the same action with a comparable defect: the notion is **equivalent to**,
not weaker than, a sofic action.

Concretely: for the Kun--Thom pair there is no masa-normalizing tracial model
of `G` acting on `G/Gamma`, by Corollary D.

## 6. Where the Hilbert--Schmidt category genuinely differs

Lemma 3 is sharp in its hypothesis: it needs the defect `(DNR2)` measured
against the **full** masa.  If a unitary only has to move a *coarse*
subalgebra correctly, no rigidity survives.

**Example 10 (Fourier block; recorded in `notes/NOTEPAD.md`).**  Put
`d_n = b_n m_n`, let `B_n subset D_(d_n)` be the subalgebra of diagonals
constant on each of `b_n` consecutive blocks of length `m_n`, and let
`U_n = directSum_(j=1)^(b_n) F_(m_n)` with `F_m` the normalized Fourier
matrix.  Then `U_n` centralizes `B_n` pointwise, yet for every monomial `W_n`

```text
|tr(U_n^* W_n)| <= 1/sqrt(m_n),   so  ||U_n - W_n||_2^2 >= 2 - 2/sqrt(m_n),
```

so `U_n` is asymptotically at distance `sqrt(2)` from every monomial.
Taking `b_n -> infinity` makes `B_U` diffuse.  Consistently with Lemma 3,
`def_D(U_n) -> 1`: the Fourier matrix maximally destroys the fine masa while
fixing the coarse algebra.

**Proposition 11 (coarse blocks still collapse if they are normalized).**
If `B subset D_N` has `k` atoms of equal trace and
`sup{ ||u f u^* - E_B(u f u^*)||_2 : f=f^* in B, ||f||<=1 } <= delta`, the
same doubly stochastic argument run on the `k x k` matrix
`A_(ab) = tr(u p_b u^* p_a)/tr(p_a)` shows `u` is `3 sqrt delta`-close to
`U(N/k) wr Sym(k)`, and `epsilon`-multiplicativity of `u` forces the induced
`pi: F -> Sym(k)` to be `epsilon^2/2`-multiplicative in Hamming.

So the escape is not "coarse instead of fine".  It is that in the Bernoulli
system **no fixed finite-atom subalgebra is normalized at all**: writing
`S_y` for the lamp symmetry at `y in Y` and `B_E = <S_y : y in E>`, the model
unitary `V_g` must satisfy

```text
V_g B_E V_g^* = B_(gE),                                        (DNR13)
```

a *moving* family of subalgebras.  For a finite window `E` inside a larger
window `E'`, the induced doubly stochastic matrix on the `2^(|E'|)` atoms of
`B_(E')` is constrained to be a deterministic permutation only on the
`E`-coordinates; on `E' \ E` it may be maximally mixing.  This is exactly the
multiplicity-fiber freedom of Example 10, expressed in the coordinates of the
problem.  In the ultraproduct, `(DNR13)` becomes `u_g A u_g^* = A` for the
diffuse separable `A = L^infty({-1,1}^Y) subset D_U`, and `A` has no
`u_g`-invariant finite-dimensional subalgebra unless the `g`-orbit on `Y` is
finite.  Proposition 11 therefore has nothing to act on.

## 7. Scope

Proved here: Lemmas 3, 4, 5, Theorem 6, Corollaries 7 and 8, Theorem 9,
Proposition 11.  Lemma 2 and Example 10 are restated from
`notes/NOTEPAD.md`.

Cited, read in the primary source: Kun--Thom arXiv:2608.06222 Definition 2.2,
Theorem A, Theorem C, Corollary D, Theorem E (PDF text, 2026-08-14);
Alekseev--Bradford arXiv:2601.18742 Definitions 3.1, 3.6, 3.8, 4.16, 4.23,
Lemma 3.4, Theorem 5.1 (PDF text, 2026-08-14).  Pestov's Theorem 8.5 is
used only for the standard equivalence "group hyperlinear iff its group von
Neumann algebra is Connes embeddable"; it is quoted, not reproved.

**Not proved here, and not to be inferred:**

* that `M_KT` is or is not Connes embeddable;
* the *invariant Cartan completion* statement — that every abstract
  embedding of `M_KT` can be conjugated so that some diagonal ultraproduct
  containing `Theta(A_KT)` is normalized by every `Theta(u_g)`.  By
  Corollary 7 that statement is *equivalent* to nonhyperlinearity of `W`;
  nothing here decides it;
* any Hilbert--Schmidt analogue of Kun--Thom Theorem 4.1 (normalization of
  the centralizer of a Kazhdan sofic approximation).  Their proof runs on
  connected-component vertex masses and isotropy orders of a finite cluster
  groupoid; a hyperlinear approximation of a Kazhdan group has a spectral gap
  for the adjoint action, but its fixed algebra need not be atomic and
  carries no component sizes.  This is the decisive open sub-claim.
