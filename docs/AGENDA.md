# Research agenda (owned and maintained by the formalization side)

Started 2026-08-08. This is my program for Question 3.4 — is every
hyperlinear group sofic? — maintained across sessions. Doctrine: every
claim is kernel-checked, cited-from-source, or explicitly conjectural.

## 1. Finite-action character transfer  [ACTIVE]

Fix a finite multiplication table and let `F_T` be the free group on its
labels.  The table defects are words `r=x_q⁻¹x_sx_t`, and unequal-pair
witnesses are words `w=x_t⁻¹x_s`.  A permutation table is exactly a finite
`F_T`-action `ρ`, with

* `d_Ham(σ_sσ_t,σ_q) = 1 - χ_ρ(r)`;
* `d_Ham(σ_s,σ_t) = 1 - χ_ρ(w)`,

where `χ_ρ(g)` is the fixed-point fraction of `ρ(g)`.  These identities are
kernel-checked in `Sofic/FiniteActionCharacter`.

Globally, for `Γ=F_k/N`, hyperlinearity says that the normal `0/1` character
`1_N` is a pointwise limit of normalized finite-dimensional unitary
characters; soficity says that it is a pointwise limit of finite-action
fixed-point characters.  Thus the live theorem is the normal-IRS transfer

`co-hyperlinear δ_N  =>  co-sofic δ_N`.

The normality and `0/1` limit are essential.  Nonnegative unitary characters
need not be finite-action characters (the `C₄` inequality in `NOTEPAD.md` is
an explicit obstruction), and no modulus can be uniform over changing word
tables.  Pointwise rounding `U(d) -> Sym(X)` is also impossible: zero defect
would make it a homomorphism, and every homomorphism from divisible `U(d)` to
a finite group is trivial.  The conversion must therefore be table-dependent
and may choose its input tolerance after the finite word table is fixed.

Next: exploit the asymptotic normal `0/1` limit in the dual finite-action
inequality `(NIR7)`.  A successful proof must rule out every finite separator
of `1_N` from the closed convex set of finite-action characters; generic
unitary-character density, full metric-sofic approximation of `U(d)`, and
Fell density of finite-image representations are all strictly too weak or too
strong in the wrong direction.

Exact doubled form (proved in `NOTEPAD.md`, `(DCT1)-(DCT9)`): for
`H_N={(a,b) in F x F : aN=bN}`, hyperlinearity is precisely approximation of
`1_(H_N)` by the canonical maximally-entangled coefficients of
`pi(a) tensor overline(pi(b))`; soficity is precisely approximation by the
canonical diagonal-set coefficients of `P_a tensor P_b` from a common finite
`F`-set.  Thus the missing implication is a restricted diagonal rounding
theorem for normal fiber-product indicators.  General synchronous-correlation
results do not supply it: maximally-entangled quantum correlations need not be
classical, while their known density theorem stays inside the quantum cone.

## 2. Defect-localized commutant pinning  [LEMMAS LANDED]

The (T)-analog of the kernel-checked f.d. collapse (N20), avoiding the
HS-stability wall.  The interface is now kernel-checked in
`Sofic/CommutantPinning`: (L1) `exists_mem_close_of_almost_le` — a
subspace δ-almost contained in an equal-dimensional subspace is
δ/(1-δ)-almost equal to it; (L2) `dist_le_defect_div_gap` and
`dist_le_perturbed_defect_div_gap` — gap pinning against exact and
ε-perturbed operators, with `sum_apply_dist_le` transferring closeness
through averaging.
Conjecture: for the Kun–Thom pairs, the model defect can be localized off
a relative-(T) core whose exact commutant then pins the almost-commutant;
one pinned compressor conjugate kills the free-lamp witness — T4 on the
family without Gate 1.

## 3. The approximation radicals  [FORMALIZABLE FRAME]

`𝔰(G)` (sofic radical) and `𝔥(G) ⊆ 𝔰(G)` (hyperlinear radical) over the
repo's `UniversalSofic`/hyperlinear ultraproducts.  Q3.4 ⟺ 𝔥 = 𝔰 on f.g.
groups.  Conjecture: `𝔰(H_K)` is the whole lamp kernel.  A strict
intermediate value of `𝔥(H_K)` would be a canonical invariant of the
hyperlinear–sofic gap — bigger than either answer.

## 4. The closure-exactness dichotomy  [ORGANIZING PRINCIPLE]

Four kernel-checked-or-measured instances this session: profinite closure
swallows the normal closure; f.d. commutants are rigid; liftable models
absorb totally; exact-coherence strata absorb totally.  Working thesis:
for compressed pairs, every closure-exact approximation category totally
absorbs, and Q3.4 on these families asks exactly whether HS-with-(T) is
closure-exact.  Dig where closure-exactness breaks: the normal `0/1`
character-transfer problem (item 1), and controlled inexactness (item 2's
ε-budget).

## Banked (kernel-checked, this repo)

Theorem A (nonsofic groups exist); the norm–trace interface; the free-lamp
reduction to KT 4.1 (verbatim-pinned); the f.d. collapse (H_K not MAP);
the profinite-closure criteria; the scalar-phase obstruction.  External
pins verified from source: KT 4.1 (arXiv:2608.06222v1), Preusser
(arXiv:1912.11386).  Dead, do not re-attempt: the seven phase-story
routes; exact-stratum ansätze on closure-swallowing frame pairs; the central
free-lamp cover as a counterexample mechanism.  Indeed
`K *_Z (Z × ℤ)` is sofic whenever `K` is sofic by amenable-amalgam closure,
and its central quotient cannot be used because soficity is not known to pass
to arbitrary quotients.  `Sofic/CentralFreeLampCover` deliberately proves no
contrary closure claim.
