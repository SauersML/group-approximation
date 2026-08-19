# Hilbert--Schmidt relaxation of the Alekseev--Bradford action model gives nothing

Date: 2026-08-14

## 0. The proposal

Alekseev--Bradford, arXiv:2601.18742 (read from the PDF, 2026-08-14), prove
in Theorem 5.1 that a class `C` closed under a product- and
wreath-compatible metric family is closed under semidirect products with a
*sofic `C`-action* (their Definition 4.23), and this covers `C =` hyperlinear
(Corollary 5.2(c)).  Definition 4.23 models the action by a map
`phi: Gamma -> Sym(A)` into the symmetric group of a **finite set** `A`,
together with a density-`(1-epsilon)` subset `S subset A` and injective
partial homomorphisms `pi_s : E -> Lambda` (`Lambda in C`) satisfying
`pi_(phi(g).s)(h) = pi_s(beta(g)^(-1)[h])`.

The proposal audited here is to *HS-ify* Definition 4.23: replace the finite
set `A` and `Sym(A)` by a diagonal masa `D_n subset M_n(C)` and a map
`phi: G -> U(n)` that approximately normalizes `D_n` in normalized
Hilbert--Schmidt norm, then rerun the proof of Theorem 5.1 in `||.||_2`.
The hope was that, since the Kun/Kun--Thom obstruction runs on generator
*graphs* of permutation tuples and unitary tuples have no generator graph,
the relaxed notion would survive where soficity of the coset action provably
fails (Kun--Thom Corollary D).

**Verdict: the proposal fails, under either reading of "approximately
normalizes".**  The two readings fail for different reasons and together they
exhaust the design space of the Alekseev--Bradford framework.

## 1. Reading (i): uniform approximate normalization -- collapses

If "`phi(g)` approximately normalizes `D_n`" means the defect

```text
def_D(u) = sup{ ||u f u^* - E_(D_n)(u f u^*)||_2 : f=f^* in D_n, ||f||<=1 }
```

is small -- the only reading under which the masa plays a structural role and
under which the ultraproduct statement `u D_U u^* = D_U` is recovered -- then
`notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md`, Lemma 3, shows

```text
def_D(u) <= delta  ==>  ||u - w||_2 <= 3 sqrt(delta)  for some monomial w,
```

and Lemma 5 there shows that `||.||_2`-multiplicativity of `phi` transfers to
Hamming-multiplicativity of the underlying permutations with a comparable
defect.  Since `||phi(g) - w_g||_2` is small, every covariance condition
verified by `phi` is verified by `w_g`, hence by the permutations
`pi(g) in Sym(n)` after absorbing the diagonal phases.

So a masa-normalizing tracial action model **contains** a permutation model
of the same action with comparable constants.  The relaxed notion is
equivalent to Definition 4.23, not weaker than it, and Kun--Thom Corollary D
kills it for the coset action `G` on `G/Gamma` exactly as it kills the sofic
version.

The intuition that "a unitary tuple has no generator graph" is wrong at this
level of generality: a unitary tuple that respects a full masa in
`||.||_2` *has* a generator graph, namely the one recovered by Lemma 3.

## 2. Reading (ii): normalization tested only on the lamps -- tautologous

If instead one only asks that `phi(g)` conjugate the finitely many
*distinguished* diagonal elements correctly -- the lamp symmetries actually
appearing in the finite test -- then Lemma 3 does not apply (correctly so;
see the Fourier-block Example 10 in the same note).  But then the masa has
been discarded, and what remains is precisely:

> for every finite `F_1 subset Delta`, `F_2 subset Gamma` and `epsilon>0`
> there exist `n`, `rho: Delta -> U(n)` and `V: Gamma -> U(n)` such that
> `rho` is `(F_1,epsilon)`-multiplicative and `(F_1,c)`-separating, `V` is
> `(F_2,epsilon)`-multiplicative, and
> `|| V(g) rho(h) V(g)^* - rho(beta(g)[h]) ||_2 < epsilon`.

By Alekseev--Bradford Lemma 3.4 (their transcription of Hayes--Sale Lemma
2.8) together with a product map, this data set is *equivalent* to
hyperlinearity of `Delta semidirect_beta Gamma`.  The converse direction is
immediate: if `Delta semidirect Gamma` is hyperlinear, restrict an
`(F,epsilon,c)`-representation to `Delta` and to `Gamma` and read covariance
off multiplicativity,
`phi(g)phi(h)phi(g)^(-1) approx phi(ghg^(-1)) = phi(beta(g)[h])`.

So under reading (ii) the "permanence theorem" is the identity map on the
problem.  No permanence content is produced.

## 3. Where the permutations are actually load-bearing in Theorem 5.1

Auditing the proof of Theorem 5.1 line by line against the Hilbert--Schmidt
family `G_hyp = {(U(n), d_HS_n)}` gives:

| step of the proof | fate under HS-ification |
|---|---|
| Lemma 3.4 (reduce `(F,eps)`-multiplicativity of `sigma` on `K semidirect Gamma` to (i)-(iv)) | verbatim; it uses only a bounded bi-invariant metric |
| product-compatibility, Lemma 3.7, and the final `Delta_(i2,i3)` amalgamation with a separating `theta: Gamma -> G_(i3)` | verbatim; Lemma 3.23 already proves `G_hyp` product-compatible, and `G` is sofic hence hyperlinear |
| condition (i): multiplicativity on the lamps, via wreath-compatibility (a) | survives; "density-`(1-eps)` subset of `A`" becomes "projections of total trace `>= 1-eps`" |
| condition (ii): `d_(i2)(psi(phi(g_1g_2)), psi(phi(g_1))psi(phi(g_2))) < eps_2` from `d_A(phi(g_1g_2), phi(g_1)phi(g_2)) < eps_1` via wreath-compatibility (b) | **breaks**: (b) is the statement that the acting map `psi: Sym(A) -> G_(i2)` is Hamming-to-`d_(i2)` uniformly continuous, and it is the only route from a combinatorial model to a metric one.  In an HS model it must be *assumed*, not derived |
| condition (iii) `Phi(h,e)Phi(e,g)=Phi(h,g)` | verbatim, by construction |
| condition (iv): covariance, via wreath-compatibility (c) `psi(sigma) tau(g) psi(sigma)^(-1) = tau(sigma.g)` | **breaks as an identity**: (c) is an *exact* algebraic conjugation of the block-diagonal algebra by a block permutation.  Replacing it by an approximate identity is exactly the hypothesis one wanted to prove |
| separation of the lamp part, via wreath-compatibility (a) with `X=S_0` | survives; it is an `l^2`-average over blocks |

The two broken steps are conditions (ii) and (iv), and in both cases the
broken ingredient is a *homomorphism* `psi: Sym(A) -> G_(i2)` -- the
block-permutation representation.  Its image is a section of
`N_(U(n))(D) -> Sym(A)` for the block algebra `D`.  There is nothing else in
the proof to relax: Alekseev--Bradford's entire contribution is the interface
`Sym(A) -> G_(i2)`, i.e. the conversion of a combinatorial action model into
a metric one.  Removing the combinatorial model removes the theorem, and by
Section 1 keeping any masa-level version of it reinstates the combinatorial
model.

This is consistent with, and refines, the coordinate-reverse-transfer
argument already in `notes/NOTEPAD.md`: a Definition-4.23 chart system for the
lamp halo pulls back along `x |-> delta_x(1)` to a sofic model of the coset
action, so no chart system exists for the Kun--Thom pair.  The present audit
adds *where in the proof* the charts are consumed, and that no HS weakening of
the chart notion is available.

## 4. What survives

Nothing of the Alekseev--Bradford framework.  What survives is the sharper
form of the target obtained in `notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md`,
Corollary 8:

> `W = (directSum_(G/Gamma) C_2) semidirect G` is hyperlinear iff there is a
> trace-preserving embedding of
> `M_KT = L^infty({-1,1}^(G/Gamma)) crossed_product G` into a matrix tracial
> ultraproduct which puts the Bernoulli algebra inside a diagonal
> ultraproduct `D_U` (always possible) and in which some `Theta(u_g)` fails
> to normalize `D_U`.

and the identification of the decisive open sub-claim as the Hilbert--Schmidt
analogue of Kun--Thom Theorem 4.1.
