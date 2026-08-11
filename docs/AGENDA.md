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

The Fournier-Facio--Willett very-flexible theorem now sharpens the last item:
for the free source it does produce finite-quotient representations whose
corners approximate the whole unitary table (`(VFC1)-(VFC5)`).  It gives no
ambient-dimension bound, however, and pointwise almost-invariance of the
corner does not control the full finite-quotient twirl (`(VFC6)-(VFC9)`).
Even centralizing that corner would yield a finite-image unitary character,
not yet a finite-action character.  Treat trace centralization and the
permutation-character conversion as two separate gates.

Property MD of the free source does not repair the second gate.  Finite
actions are dense only in the weak action topology, where fixed-point measure
is discontinuous: the order-`m` rotation of the circle has no fixed points
but converges weakly to the trivial action (`(MDG1)-(MDG4)`).  Thus pulling
back a free quotient action and invoking MD loses exactly the normal-Dirac
statistics required for soficity.

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

The Cartan-to-monomial estimate `(CTM1)-(CTM16)` in
`docs/TRUE_CARTAN_MONOMIAL_GATE.md` gives a dimension-free intermediate
criterion.  If the completed table approximately preserves one common masa,
Birkhoff matching puts every generator within squared normalized-HS distance
`2 kappa_D` of a monomial unitary, and multiplication passes to the underlying
permutations.  A separate fixed-phase half-plane condition then converts trace
separation into Hamming separation.  Thus a common Cartan and noncancelling
fixed phases would finish the TRUE lane; neither follows yet from the normal
`0/1` character law, and approximate Cartan invariance alone is insufficient.
Without the half-plane condition, the same construction gives an exact
abelian-by-sofic decomposition: the kernel of the permutation-ultraproduct map
is asymptotically diagonal and hence abelian.  This does not imply soficity in
the required extension orientation; `(AB1)-(AB3)` are an explicit
abelian-by-residually-finite nonsofic calibration.

The phase kernel has additional exact structure, proved in
`docs/TRUE_HAAR_PHASE_KERNEL.md`: its coordinate phases form a measurable
field of characters whose law is Haar on the Pontryagin dual, equivariantly
for the sofic quotient (`(HPK1)-(HPK12)`).  The remaining conversion is now a
finite-window Fourier-completion gate `(HPK13)-(HPK18)`: replace the
`L^2`-multiplicative Haar character chart by finite-order phase labels whose
cocycle equations hold outside `o(1)` of the coordinates.  Such a completion
untwists to permutations and is sofic, even when the phase orders grow.
Haar genericity alone does not provide the completion; the Kun--Thom
augmentation kernel specializes to the same infinite-dimensional dual action.
A valid positive special case is split extension by a finitely generated
abelian kernel, which embeds in `Hol(K) times Q`; the Kun--Thom kernel has
infinite abelian rank and therefore lies exactly outside this case.

For a phase kernel of exponent `m`, the section primitive has an intrinsic
Bockstein residue.  Writing `delta b(q,r)=a_(v(q,r))`, the functions
`lambda_q=b_q^m` form a measurable circle-valued 1-cocycle.  If `lambda` has
an `m`th root **inside the 1-cocycle group**, then dividing `b` by that root
produces a `mu_m`-valued monomial embedding; skew untwisting proves soficity
(`(HPK9e)-(HPK9k)`).  Pointwise divisibility of the circle does not imply
cocycle divisibility.  Thus any bounded-exponent common-Cartan counterexample
must carry a nonzero Bockstein residue; this is the exact cohomological datum
which finite cocycle stability would have to eliminate.  Concretely the
residue is the evaluated extension class
`partial_m[lambda]=[a_(v(q,r))]`; it maps to zero in circle-valued `H^2`, so
injectivity of `H^2(mu_m)->H^2(T)` for the Loeb action would close this gate.
This injectivity is not automatic even in an exact regular model: the
four-dimensional regular representation
`C_4 -> U(4)`, `g |-> swap directSum i directSum (-i)`, has phase kernel
`C_2`, Haar kernel law, and nonzero Bockstein (`(HPK9m)-(HPK9p)`).  The same
group is sofic through another Cartan.  Therefore the residue is a
model-level obstruction; a general proof must replace the Cartan or round
through it, not try to deduce its vanishing from trace moments.

Slow tensor amplification performs one useful model replacement.  Taking
`L_n`-fold tensor powers with `L_n->infinity` sufficiently slowly preserves
all multiplicativity and the kernel `K`, while changing every nontrivial
quotient permutation length `ell` to `1-(1-ell)^(L_n)->1`.  Hence the
quotient Loeb action may be assumed essentially free.  For exponent-`m`
kernel, the remaining residue lies in the coefficient kernel
`ker(H^2(R_Q,mu_m)->H^2(R_Q,T))` of a principal sofic equivalence relation.
It vanishes when `R_Q` is treeable.  The exact remaining TRUE-side question
is whether the special residue forced by a monomial hyperlinear model can be
removed for arbitrary principal sofic `R_Q`.

Popa superrigidity gives a sharp negative calibration to automatic removal.
For the free Bernoulli relation of
`Q=SL_3(Z) times C_m`, the projection character `Q->mu_m` is not
`m`-divisible in measurable `H^1`.  It occurs as the phase residue in a
regular common-Cartan model of the residually finite group
`SL_3(Z) times C_(m^2)`.  Thus even principal sofic relations may retain the
minimal-alphabet residue; the group is sofic only because its phases already
lie in the larger fixed alphabet `mu_(m^2)`.  The true target remains
finite-phase completion, not universal Bockstein vanishing.

This target sharpens once more if all torsion phases are allowed.  Put
`mu_infty=union_M mu_M`.  A measurable `mu_infty`-valued primitive can be
truncated on each finite test to one alphabet `mu_(M_n)`: only finitely many
functions occur, their discarded mass tends to zero, and the projective
cocycle equation then fails only on the union of three discarded sets.
Finite-phase skew untwisting proves soficity.  The same proof works for every
torsion phase kernel, without a global exponent: a finite test sees only
finitely many kernel orders and `M_n` can absorb them.  Consequently the
exact torsion-kernel obstruction is now

`ker(H^2(R_Q,mu_infty) -> H^2(R_Q,T))`,

not the larger minimal-alphabet Bockstein kernel.  Both the `C_4` and
Popa/Bernoulli calibrations vanish after this enlargement (`mu_4` and
`mu_(m^2)`, respectively).  Finite-index permanence for sofic relations is
not a shortcut: it assumes the base subrelation is already embedded in the
finite extension, while constructing that subrelation is exactly the
torsion splitting being sought.

The coefficient kernel also has an exact primitive quotient description:

`ker(H^2(R_Q,mu_infty)->H^2(R_Q,T))`
` ~= {b:delta b is torsion-valued}/(T-valued cocycles * torsion cochains)`.

This gives a positive criterion.  If, after multiplying the circle primitive
by a circle 1-cocycle, its scalar essential range is countable, divisibility
of the roots of unity extends the identity on the torsion intersection to a
scalar homomorphism.  Applying it pointwise produces a measurable torsion
primitive and proves soficity (Theorem 3A in
`docs/TRUE_HAAR_PHASE_KERNEL.md`).  The unrestricted coefficient statement
already fails for a free hyperfinite relation in degree one: the cocycle
`u(a,x)=a` for dense translations `Q/Z acting on R/Z` is a circle
coboundary but not a `Q/Z` coboundary.  The live target must therefore use
the special automorphic Haar evaluation `omega(q,r,x)=chi_x(v(q,r))`, not a
generic measurable retraction.

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

The canonical Schoenberg/Poisson scalar transform does not cross the gap
either.  Applied to the nonnegative `C_4` character `(NIR5)`, it gives
`(1,e^(-t),e^(-2t),e^(-t))`, which violates the finite-action inequality
`theta(g)<=theta(g^2)` for every `t>0`; the violation persists after every
finite tensor amplification (`(SPF1)-(SPF6)`).  Only the limiting normal
`0/1` character removes it.  Do not replace the joint matching problem by a
generic negative-type-to-fixed-point transform.

Do not confuse Lueck's ``approximation property'' for permutation characters
with density of permutation characters.  In the precise definition audited in
Boschheidgen's thesis, it says only that von Neumann ranks converge along a
pointwise-convergent sequence already lying in the permutation-character
class.  It neither produces that sequence nor moves a finite-dimensional
unitary sequence into the class.  The same warning applies to Kionke's
fixed-algebraic-degree version; see `(LRA1)-(LRA5)` in `docs/NOTEPAD.md`.

Exact-image functoriality is also impossible, even for a fixed normal-Dirac
table. The cyclic two-dimensional sequence `(IFR1)-(IFR8)` converges
pointwise to the regular character of `C_2`, but its exact images satisfy the
changing accidental relation `b=a^(2n)`. Every finite action of those images
has `supp(b) subset supp(a)` and cannot approach the target values
`chi(a)=1`, `chi(b)=0`. Hence residual finiteness of the matrix/projective
image, its regular or coset actions, and same-image permutation-character
conversion are dead routes. The output must forget accidental levelwise
relations; see `docs/TRUE_IMAGE_FACTOR_NO_GO.md`.

FALSE-side fermionic criterion: the full exterior-algebra functor turns one
operator-norm-visible eigenvalue into a uniform normalized-HS displacement.
After tensoring it with its conjugate, the normalized character is
`|det((1+U)/2)|^2` and the normalized-HS multiplicative defect is at most
`sqrt(d_n/2)` times the original operator-norm defect. Hence a radical
witness with a model satisfying `sqrt(d_n) * defect_n -> 0` already yields a
hyperlinear nonsofic quotient. This removes every rank-profile requirement
and leaves only a quantitative
dimension--error gate; see `docs/FALSE_FERMIONIC_AMPLIFICATION.md`.
The same note now proves that this square-root loss is optimal up to a
universal constant among all exact continuous functorial amplifications:
if `R:U(d)->U(N)` makes a rank-one involution HS-visible by `Delta_R`, then
its normalized-HS differential has operator-to-HS norm at least
`sqrt(d) Delta_R/pi`. Therefore the next FALSE step must use special group
structure rather than swap in a more efficient universal representation
functor. More generally a rank-`r` visible involution costs at least
`sqrt(floor(d/r)) Delta/pi`, recovering the `1/sqrt(delta)` sparse-corner
scale for relative rank `delta=r/d`.

FALSE-side no-go `(CAF1)-(CAF13)`: a fixed-point-free element of an amenable
action survives the sofic image obtained by completing its restrictions to
Følner sets.  Therefore every coamenable subgroup contains every central
element of `Rad_sof(J)`, and a class-`A` group has
`Z(J) intersect Rad_sof(J)={1}`.  This rules out all coamenable monomial
negative sectors for the cyclic shear, including nonnormal character
induction.  See `docs/FALSE_COAMENABLE_ACTION_CRITERION.md`.
Do not pursue class-`A` permanence as an allegedly weaker shortcut.  The
Følner-truncation theorem already forbids the required fixed-point-free
action.  Conditionally, the displacement collapse `(CAC9)--(CAC15)` proves
that any such shear action
already restricts on one vertex to an amenable action in which the original
radical witness moves mean mass at least `1/4`; that restricted action itself
produces the hyperlinear nonsofic image.  The smaller action target is
directly an amenable `H`-action with `m(Fix(x))<1`.

The prescribed-mean strengthening `(CAP1)--(CAP13)` closes that smaller
target too.  After pullback along a free presentation, every invariant-mean
permutation character is a pointwise limit of finite-action characters:
approximate the chosen mean by an
`ell^1`-Reiter sequence, replace rational weights by numbered fibers, and use
the coherent partial maps `(x,k)|->(gx,k)`.  Their unmatched mass is the
`ell^1` boundary and their common fiber indices make multiplication coherent.
Thus a sofic-radical element has fixed-set mean `1` in every amenable action.
Any viable amenable negative sector must be genuinely nonpermutational, not
merely nonmonomial.

The Kazhdan-corner theorem gives a separate exact FALSE certificate: every
nontrivial weak-MF Kazhdan group has a nontrivial hyperlinear quotient, by
renormalizing on the complement of the central Kazhdan projection.  Hence a
simple Kazhdan weak-MF group is hyperlinear, and weak MF of
`St_5(L_(F_2)(1,2))` would make its simple nonsofic quotient
`EL_4(L_(F_2)(1,2))` hyperlinear.  See
`docs/FALSE_KAZHDAN_CORNER.md`.  Do not treat Delzant's theorem that every
countable group embeds in a Kazhdan group as MF-preserving: its envelope is
a quotient `P/N` of an SQ-universal hyperbolic Kazhdan group, and weak MF is
not known to pass through the arbitrary quotient `P->P/N`.

Do not try to extend Pestov's invariant `UCB` sphere mean to all bounded
functions formally.  The implication is false even in dimension two:
a faithful `F_2<SU(2)` representation is Bekka-amenable and has the Haar
mean on `UCB(S^3)=C(S^3)`, but its sphere action is free, so an invariant
`ell^infinity(S^3)` mean would contradict paradoxicality of `F_2` (`(USP4)--
(USP5)`).  A sphere route must use the normal `0/1` trace law essentially.
In fact odd symmetric powers sharpen the warning: their exact normalized
characters converge to the regular `0/1` character of `F_2`, and every
level still acts freely on its unit sphere, so no invariant
`ell^infinity`-mean exists (`(USP6)--(USP9)`).  The normal law cannot justify
a levelwise extension; it would have to enter through a cross-level matching
argument.

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
