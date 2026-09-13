# Phases never obstruct rounding: soft kernels of block-monomial HS models, and Q3.4 as frame extraction

Lane `ex-q34-collapse`, 2026-09-12.  Status of each item is stated where it is
proved.  Nothing here decides Q3.4; the content is where the difficulty is
not.

## 0. Summary

A unitary HS model is *block-monomial of block size `k`* when every matrix
permutes the summands of `C^n = ⊕_{i<=n} C^k` and rotates inside them:
`W_(n,k) = U(k) wr S_n`.  For `k=1` these are the monomial unitaries, which
are exactly the normalizers of the full diagonal masa, and by
`diagonal-normalizer-rigidity` approximate normalizers of that masa are near
them.

1. **Soft-kernel split (Theorem 2).**  For any block-monomial asymptotic
   homomorphism of `G`, the permutation parts define a homomorphism
   `G -> prod_omega (S_n, d_H)`.  Its kernel `A` (the *soft kernel*) is normal
   and `G/A` is sofic, with no hypothesis on the phases or on `k`.  If `k` is
   bounded and the trace is regular, `A` is amenable (`C[A]` satisfies the
   standard identity `S_(2k)`); for `k=1`, `A` is abelian.
2. **Corollary 3.**  A group with trivial amenable radical is sofic iff it has
   regular HS models in `U(k) wr S_n` for some fixed `k`.  For `k=1`, "no
   nontrivial abelian normal subgroup" suffices.
3. **Theorem 4 (Q3.4 as frame extraction).**  Every hyperlinear group is sofic
   iff every hyperlinear group has regular HS microstates approximately
   normalizing a full masa.  The proof passes to `G * Z`, which has no
   nontrivial abelian normal subgroup.  Phase cancellation, the `U(1)`-cocycle
   of a monomial model and bounded internal rotations are therefore never
   the obstruction to Q3.4.  The whole difficulty is an approximately
   invariant *frame*.
4. **Corollary 5 (model test).**  The binary Leavitt unit group `R^x`, every
   group containing `EL_9(R)`, and the Kun--Thom double `G *_Gamma G` have
   no regular bounded-block monomial HS models.  For `R^x` more holds, with no
   trace hypothesis: every block-monomial asymptotic homomorphism has
   asymptotically trivial permutation part.  Any hyperlinear model of these
   groups, if one exists, is frame-incoherent.
5. **Sharpness.**  With unbounded blocks the class is universal: `n` diagonal
   copies of any microstate.  Bounded against unbounded block size is the
   exact threshold.

## 1. Setting

`W_(n,k)` acts on `C^n ⊗ C^k` by `M(e_i ⊗ v) = e_(sigma(i)) ⊗ u_i v` for
`M = (u_1..u_n; sigma)`, `u_i in U(k)`, `sigma in S_n`.  Then
`(u;sigma)(u';sigma') = ((u_(sigma'(i)) u'_i)_i ; sigma sigma')`, so the
permutation part `pi(M) = sigma` is a homomorphism `W_(n,k) -> S_n` with
kernel the block-diagonal group `U(k)^n`.

Norms: `||X||_2^2 = (1/nk) Tr(X^*X)`; `d_H(sigma,sigma') = (1/n)#{i :
sigma(i) != sigma'(i)}`.  Ultraproducts along a nonprincipal `omega` over a
sequence `(n_m, k_m)`:
`W_omega = prod_omega W_(n_m,k_m) / {||.||_2 -> 0}`,
`S_omega = prod_omega (S_(n_m), d_H) / {d_H -> 0}`, and `tau = lim_omega tr`.

A *block-monomial HS model* of a countable group `G` is a homomorphism
`rho : G -> W_omega`.  It is *regular* when `tau(rho(g)) = 0` for `g != e`,
which makes `rho` injective.  By the standard diagonal argument this is
equivalent to finitary models on windows `F` with multiplicative defect and
trace separation `< eps`.  Soficity means isomorphism to a subgroup of some
`S_omega` (Pestov, *Hyperlinear and sofic groups: a brief guide*,
arXiv:0804.3968, Definition 3.1).

## 2. The Hamming comparison

**Lemma 1.**  For `M = (u;sigma)`, `M' = (u';sigma')` in `W_(n,k)`,

```text
d_H(sigma, sigma') <= (1/2) ||M - M'||_2^2 ,            (HC1)
||M - (u; id)||_2^2 = 2 d_H(sigma, id).                   (HC2)
```

*Proof.*  `||M-M'||_2^2 = (1/nk) sum_i sum_v ||(M-M')(e_i ⊗ v)||^2` over an
orthonormal basis `v` of `C^k`.  If `sigma(i) != sigma'(i)` the vectors
`e_(sigma(i)) ⊗ u_i v` and `e_(sigma'(i)) ⊗ u'_i v` are orthogonal unit
vectors, so the inner sum is `2k`; the other terms are `>= 0`.  This gives
(HC1).  For (HC2), `M - (u;id)` kills the columns with `sigma(i) = i` and
contributes exactly `2k` on each other column.  ∎

So `pi` induces a well-defined homomorphism `pi_omega : W_omega -> S_omega`.

## 3. The soft-kernel split

**Theorem 2.**  Let `rho : G -> W_omega` be a homomorphism, let
`psi = pi_omega ∘ rho : G -> S_omega` and let `A = ker psi`.

(a) `A` is normal and `G/A ≅ psi(G) <= S_omega`.  If `rho` is injective,
    `G/A` is sofic.  Block sizes are arbitrary here.
(b) If `rho` is regular and `k_m = k` is constant, `A` is amenable.  More
    precisely `L(A)` embeds trace-preservingly into a finite von Neumann
    algebra satisfying the standard identity `S_(2k)`.
(c) If `k = 1`, then `rho(A)` is commutative, so `A` is abelian whenever
    `rho` is injective.

*Proof.*  (a) `psi` is a homomorphism by Lemma 1 and `A` is its kernel.  A
countable subgroup of `S_omega` is sofic by Definition 3.1.

(b) For `a in A` choose representatives `rho_m(a) = (u_m(a); sigma_m(a))`
with `d_H(sigma_m(a), id) ->_omega 0`.  By (HC2) the block-diagonal
`D_m(a) = (u_m(a); id)` represents the same element of `W_omega`.  Hence
`rho|_A` takes values in the unitary group of the tracial ultraproduct

```text
𝔄 = prod_omega ( ℓ^∞_(n_m) ⊗ M_k , (1/n_m) sum_i tr_k ).
```

`𝔄` is a finite von Neumann algebra, and it satisfies `S_(2k)`:
Amitsur--Levitzki holds in each `ℓ^∞_n ⊗ M_k`, and ultraproduct operations are
coordinatewise.  Regularity says the trace-preserving `*`-homomorphism
`C[A] -> 𝔄`, `a |-> rho(a)` pulls `tau` back to the regular trace.  So the von
Neumann algebra it generates is isomorphic to `L(A)` (same trace on
generators), and `L(A)` satisfies `S_(2k)`.  A finite von Neumann algebra
satisfying a polynomial identity has no type `II_1` summand: such a summand
contains a unital copy of `M_m` for every `m`, and `S_(2k)` does not vanish on
`M_m` for `m > k`.  So `L(A)` is type I, hence injective, hence `A` is amenable
(injectivity of `L(A)` is equivalent to amenability for discrete groups).
Remark: `C[A]` satisfies `S_(2k)`, so by the Isaacs--Passman theorem on group
algebras with a polynomial identity (characteristic zero), `A` even has an
abelian subgroup of finite index.  Nothing below uses this.

(c) For `k = 1`, `ℓ^∞_n ⊗ M_1` is commutative.  ∎

*Model tests of Theorem 2.*  Two trivial models fail the hypothesis of (b):
- A pure phase model `a |-> diag(chi_1(a),...,chi_n(a))` of an abelian group
  with random characters is regular.  Its soft kernel is everything, and the
  split correctly reports only that `A = G` is abelian.  This is the
  `scalar-trace-of-diagonal-normalizer-is-permutation-blind` phenomenon: the
  phases do the separating, but only on an abelian normal subgroup.
- For `F_2 -> U(2)^n` given by `n` Haar-random homomorphisms, the soft
  kernel is `F_2`, which is not amenable.  (b) is not contradicted, because
  the averaged trace of the commutator word is
  `E tr_2(U V U^* V^*) = E |tr_2 V|^2 = 1/4`, so the model is not regular.
And a real object satisfies it: a sofic approximation `sigma` gives
`(1; sigma)` with trivial soft kernel.

## 4. Groups without amenable normal subgroups

**Corollary 3.**  Suppose `G` has no nontrivial amenable normal subgroup (for
`k = 1`: no nontrivial abelian normal subgroup).  If `G` has a regular
`U(k) wr S_n` HS model then `G` is sofic.  Conversely a sofic group has regular
permutation-matrix models (`k = 1`, trivial phases).  Finitarily, for `k = 1`: `G` is sofic iff for
every window it has regular HS microstates `U_g in U(n)` with
`def_D(U_g) -> 0` for the full diagonal masa `D_n`.

*Proof.*  Theorem 2 gives an amenable (resp. abelian) normal `A`, so `A = 1`
and `G = G/A` is sofic.  For the finitary form,
`diagonal-normalizer-rigidity` clause 1 replaces each `U_g` with
`def_D(U_g) <= delta` by a monomial `w_g` with `||U_g - w_g||_2 <= 3 sqrt(delta)`.
That perturbs multiplicative defects by `O(sqrt(delta))` and traces by
`3 sqrt(delta)`.  ∎

## 5. Q3.4 is frame extraction

**Lemma 4a.**  Let `H != 1`.  Then `Γ = H * Z` has no nontrivial abelian
normal subgroup.

*Proof.*  Two classical facts about free products: (F1) if two elements
commute, either both lie in one conjugate of a factor or both are powers of a
common element; (F2) each factor is malnormal, `X ∩ uXu^(-1) = 1` for
`u ∉ X` (Magnus--Karrass--Solitar, *Combinatorial Group Theory*, §4.1).  Let
`t` generate `Z` and fix `h in H \ 1`.  Let `N ◁ Γ` be abelian and
`1 != x in N`.
- If `x` lies in no conjugate of a factor, then by (F1) its centralizer is
  cyclic.  `N` lies in that centralizer, so `N` is infinite cyclic.  `Γ` acts on
  `N` through `Aut(Z) = {±1}`, so an index `<= 2` subgroup centralizes `x` and
  is cyclic, and `Γ` is virtually cyclic.  But `⟨t, h t h^(-1)⟩` is free of rank
  two by normal forms.
- If `x in yHy^(-1)`, then `x` and `x' = t x t^(-1)` commute.  By (F1) they
  lie in one conjugate of a factor, or are powers of a common `z`.  In the
  second case `z` is itself conjugate into a factor, since powers of an element
  of cyclically reduced length `>= 2` keep that length, and distinct
  conjugates of factors meet trivially by (F2).  So in both cases
  `x, x' in yHy^(-1)`, and
  `yHy^(-1) ∩ (ty)H(ty)^(-1) != 1` forces `y^(-1) t y in H` by (F2).  That is
  impossible: the retraction `Γ -> Z` killing `H` sends `y^(-1) t y` to `t`.
- If `x in yZy^(-1)`, run the same argument with `h' = y h y^(-1)` in place of
  `t`.  It forces `h in Z`, and the retraction `Γ -> H` killing `Z` shows
  `h != 1` is not in `Z`.
So `N = 1`.  ∎

**Lemma 4b.**  If `H` is hyperlinear, so is `H * Z`.
This is the free-product permanence of hyperlinearity.  Microstates of `H`
together with an independent Haar unitary are asymptotically free by
Voiculescu's asymptotic freeness theorem, and the free product of the
regular traces is the regular trace of `H * Z`.  [Literature pin: see §8.]

**Theorem 4.**  The following are equivalent.
(i) Every hyperlinear group is sofic.
(ii) Every hyperlinear group has regular monomial HS models, i.e. regular
     microstates approximately normalizing the full diagonal masa.
(iii) Every hyperlinear group with no nontrivial abelian normal subgroup has
     regular monomial HS models.

*Proof.*  (i)⇒(ii): permutation matrices are monomial.  (ii)⇒(iii) is trivial.
(iii)⇒(i): if `H` is hyperlinear, `H * Z` is hyperlinear (4b) with no abelian
normal subgroup (4a), so it has a regular monomial model and is sofic by
Corollary 3.  Soficity passes to the subgroup `H`.  ∎

*What this says.*  The monomial matrices are the unitaries that preserve a
frame (a full masa), carrying arbitrary `U(1)`-phases.  Theorem 2 shows the
phases can only separate an abelian normal subgroup, and `H * Z` has none.  So
for the question "is every hyperlinear group sofic" the `U(1)`-cocycle, its
curvature and its trace cancellations are removable for free.  What remains
is exactly one thing: find microstates of `H * Z` that approximately preserve
some frame.  The same holds with a bounded block size `k`, provided a
nontrivial amenable normal subgroup of `H * Z` is excluded as well.  Via
Kurosh's subgroup theorem that reduces to the abelian and factor-conjugate
cases above; this is not needed for Theorem 4.

## 6. Model tests on the nonsofic groups

**Corollary 5.**  Let `R = L_(F_2)(1,2)`.
(a) Every block-monomial HS model `rho : R^x -> W_omega` has
    `pi_omega ∘ rho` trivial, with arbitrary block sizes and no trace
    hypothesis.  So every block-monomial model of `R^x` is asymptotically
    block-diagonal.
(b) No group containing a copy of `EL_9(R)` has a regular HS model in
    `U(k) wr S_n` for fixed `k`.  In particular `R^x` has no regular HS
    microstates approximately normalizing a full masa.
(c) The Kun--Thom double `G *_Gamma G` of `kt-pair-group-double-is-nonsofic`
    at `q = 2` has no regular `U(k) wr S_n` model for fixed `k`.

*Proof.*  (a) `pi_omega ∘ rho` is a homomorphism into a universal sofic
group, which is trivial by `leavitt-unit-group-has-only-trivial-sofic-morphisms`.
(b) Restricting a model to the subgroup keeps it regular and block-monomial.
`EL_9(R)` is simple (`binary-leavitt-elementary-group-is-simple`), infinite and
nonsofic (`openai-leavitt-unit-nonsofic`: its nonsofic `G = EL_D(R)` is
isomorphic to `EL_9(R)`).  Its amenable radical is normal, so it is `1` or
everything, and a nonsofic group is not amenable.  Corollary 3 would make it
sofic.  (c) The double is nonsofic and has trivial amenable radical
(`kt-q2-double-has-trivial-amenable-radical`); apply Corollary 3.  ∎

*Consequence for the separation programme.*  Any proof that `R^x` or the double
is hyperlinear has to produce frame-incoherent microstates: no full masa is
approximately normalized, and no bounded-dimensional block decomposition is
approximately permuted.  In block-monomial language all of the model lives in
blocks of unbounded dimension that the permutation part never moves.  This
fences every construction that glues fixed-size internal pieces along a
permutation skeleton.  It is the continuous-label, trace-free-kernel
companion of `leavitt-regular-atlas-block-monomial-gap` (explicit transports)
and `uniformly-discrete-block-monomial-images-are-sofic` (finite labels with a
gap).

## 7. What this relocates in the collapse region

- `dephasing-inverse-forces-monomial`: a one-basis dephasing that respects
  inverses is near-monomial.  With Theorem 4, a dephasing route to
  `regular-character-markovization` is literally equivalent to Q3.4; the
  obstacle is the basis, not the interference.
- `traffic-branching-rounding-hierarchy` names "common-Cartan extraction and
  phase cancellation" as the two costs of monomialization.  The second cost is
  zero for Q3.4.
- `invariant-cartan-completion` is the Kun--Thom instance with a prescribed
  Bernoulli subalgebra; `approximate-bernoulli-lamp-extraction-is-cartan-completion`
  is the same gate seen from the lamps.
- `markov-sofic-equals-sofic` needs trace separation of doubly stochastic
  kernels.  On a monomial model the dephased kernel `|u_ij|^2` is the
  permutation part, and its trace separation fails exactly on the soft kernel.
  Theorem 2 identifies that set as an abelian normal subgroup.

## 8. Open, and literature pins

Open claim carried to the graph: `hyperlinear-groups-admit-masa-normalizing-microstates`
(statement (ii) of Theorem 4).  Its attempts are recorded on the node.

Literature pins used, read from the arXiv PDF text on 2026-09-12:
- Pestov, arXiv:0804.3968, Definition 3.1: soficity as a subgroup of a metric
  ultraproduct of symmetric groups with normalized Hamming distance.
- Pestov, arXiv:0804.3968, Theorem 8.5 (Kirchberg; Radulescu Prop. 2.5; Ozawa
  Prop. 7.1): a countable `G` is hyperlinear iff `VN(G)` embeds into
  `R^omega`.
- Brown--Dykema--Jung, arXiv:math/0609080v5, Corollary 4.5: amalgamated free
  products over hyperfinite `B` of `R^omega`-embeddable algebras with separable
  predual are `R^omega`-embeddable.  With `B = C` this gives Lemma 4b.
Textbook inputs: the commuting-elements theorem and malnormality of factors
in free products (F1, F2); Amitsur--Levitzki; type I von Neumann algebras are
injective; a discrete group with injective `L(A)` is amenable.
