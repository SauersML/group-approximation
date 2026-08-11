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
need not be finite-action characters (the `C₄` inequality in `docs/NOTEPAD.md` is
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

Exact doubled form (proved in `docs/NOTEPAD.md`, `(DCT1)-(DCT9)`): for
`H_N={(a,b) in F x F : aN=bN}`, hyperlinearity is precisely approximation of
`1_(H_N)` by the canonical maximally-entangled coefficients of
`pi(a) tensor overline(pi(b))`; soficity is precisely approximation by the
canonical diagonal-set coefficients of `P_a tensor P_b` from a common finite
`F`-set.  Thus the missing implication is a restricted diagonal rounding
theorem for normal fiber-product indicators.  General synchronous-correlation
results do not supply it: maximally-entangled quantum correlations need not be
classical, while their known density theorem stays inside the quantum cone.

Source audit `(SA1)-(SA6)` now pins this to Manzoor's exact closure gap:
`closure(T_IRS intersect T_fd)` versus
`T_IRS intersect closure(T_fd)` at the normal Dirac trace.  The quantitative
theorem of Burton--Chaudkhari--Juschenko--Muliarchyk proves the transfer for
amenable quotients, with doubled coefficient error at most `2 sqrt(epsilon)`
after matrix rounding.  Subgroup tests capture all finite separators but do
not make the separating IRS normal Dirac, and HS-stability results stop at
exact matrices rather than permutation actions.

The Bernoulli-lamp detour is also sharply delimited by `(BL1)-(BL4)`: the
shift action on `directSum_Gamma C_2` is a sofic `C`-action only if `Gamma` is
already sofic.  Hence both Hayes--Sale wreath-product permanence and its 2026
Alekseev--Bradford action generalization are circular for this purpose.

IRS tensor powers `(ICE1)-(ICE3)` extract the normal probability-one core and
preserve both co-hyperlinearity and co-soficity.  This turns a general IRS
separation into a group separation only when the extracted core still fails
the corresponding finite-action approximation; known subgroup-test
separations do not supply that extra property.

Spectral compression `(SCR1)-(SCR10)` now removes exceptional vectors from a
finite hyperlinear table: on an asymptotically full corner every selected
normal relator is operator-norm small, while one outside witness remains
Hilbert--Schmidt separated.  The exact residue is generator invariance of the
corner.  Averaging the defect operator over conjugates makes this a Følner
boundary problem and therefore recovers only the known amenable case.

The quantitative-stability audit `(QSA1)-(QSA5)` rules out two apparent
shortcuts.  Dor-On--Hall--Kachkovskiy requires the very operator-norm corner
leakage missing in `(SCR10)` (small normalized-HS leakage does not imply it,
even for a codimension-one corner).  Dogon--Vidick corrects special
lamplighter relations to an exact unitary representation through towers for
the amenable `Z`-shift, and explicitly does not obtain permutation rounding.
Thus pairwise unitary correction cannot replace simultaneous finite-set
assembly.

Finite-prefix completion `(FPC1)-(FPC12)` nevertheless bypasses `(SCR10)`
for every fixed word test without averaging.  Intersecting finitely many
translated good corners loses at most `|B|(1-tr(p))`; each generator then
extends from all of its tested prefix fibers to a unitary on `pH`.  Every
tested word agrees with the original word on the common large intersection,
so relators remain small and the witness remains trace-visible.  This removes
generator invariance as the analytic bottleneck.  What remains is a joint
atom/matching construction from those overlapping prefix fibers.  It may not
require the generator matrices themselves to be close to permutation
matrices—that stronger pointwise demand is false—but it must retain all
tested relator and witness losses in one finite action.

Next: extract a finite matching system from the simultaneous prefix-fiber
data `(FPC4)-(FPC8)` without demanding generatorwise matrix approximation.
Use the normal `0/1` trace law to control overlaps and retain only the tested
word losses.  Do not route through conjugate
averaging, amenability, generic HS stability, or Bernoulli-lamp permanence;
their exact stopping points are now proved in the notepad.

Also do not demand metric-sofic approximation of `U(d)`.  The scalar
prime-order subgroup with chordal HS length has unequal nonidentity lengths,
whereas an approximate permutation action of `C_p` forces every nonidentity
power to have the same asymptotic Hamming length (`(MSU1)-(MSU4)`).  The
normal-Dirac problem is narrower because it only retains a limiting discrete
`0/1` word law after table-dependent amplification.

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
groups.  The finite-presentation localization `(FPR1)-(FPR12)` sharpens this:
it is enough to prove equality for finitely presented groups, and any failure
is detected by one element in one finite presentation.  Conjecture:
`𝔰(H_K)` is the whole lamp kernel.  A strict
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
