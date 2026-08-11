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

The positive-loss obstruction now has a one-witness transitive normal form;
see `TRUE_ONE_WITNESS_TRANSITIVE_LOSS.md`.  If TRUE fails, there are fixed
`R subset N`, one `w outside N`, nonnegative weights, and `epsilon>0` such
that every finite-index subgroup `H<=F` has weighted loss at least `epsilon`
after averaging membership over the conjugates represented by `F/H`, while
finite-dimensional characters have loss tending to zero.  Orbit
decomposition proves that testing arbitrary finite actions gives exactly the
same infimum as testing the quasiregular actions `F/H`.  Thus disjoint unions
and multiple witnesses are no longer part of the gate; the missing theorem
is the normal-indicator rounding from unitary characters to one finite
quotient/subgroup pair `(Q,J)` with small averaged Boolean loss.

Cartesian powers sharpen this further to a linear, unweighted radical
inequality; see `TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md`.  For the finite
presentation `P=<S|R>`, one has `w in Rad_sof(P)` if and only if some finite
`C` satisfies

`1-chi_rho(w) <= C sum_(r in R)(1-chi_rho(r))`

for every finite action `rho`; orbit decomposition again makes transitive
coset actions sufficient.  The amplification proof is exact: if no linear
constant existed, take actions with relator defect `o(d_rho(w))` and about
`1/d_rho(w)` Cartesian powers, producing vanishing relator defect but a
fixed positive motion of `w`, contrary to radical membership.  Thus a
counterexample requires finite-dimensional characters that maximally violate
one classical linear quasiregular-character inequality; arbitrary minimax
weights are not intrinsic to the gate.

Conjugate-double tensor powers give the exact parallel statement for the
hyperlinear radical; see `TRUE_RADICAL_DOMINATION_CONSTANTS.md`.  With
`q_chi(g)=1-|chi(g)|^2`, define the optimal ratios `C_perm` over finite
action characters and `C_fd` over all normalized finite-dimensional
characters.  Then

`C_perm<infinity iff w in Rad_sof(P)`,
`C_fd<infinity iff w in Rad_hyp(P)`, and `C_perm<=C_fd`.

Consequently TRUE is exactly the assertion that `C_perm<infinity` forces
`C_fd<infinity` for every finite presentation and word.  This is a sharper
target than full HS stability: only the one controlled word must collapse,
and the comparison constant may depend arbitrarily on the fixed presentation
and word.  A counterexample is exactly a finite classical domination
constant together with an infinite matrix-character domination constant.

The finite-dimensional singularity branch is now closed; see
`TRUE_FIXED_DIMENSIONAL_ARC_BOUNDARY.md`.  If `C_perm<infinity`, then the
restricted constant `C_fd(d)` is finite for every fixed matrix dimension
`d`.  Indeed an unbounded fixed-dimensional ratio has a semialgebraic bad
arc.  In the conjugate double, its relators vanish to higher power-series
order than its witness; truncation at the first witness jet produces an
exact homomorphism to a finitely generated complex linear group retaining
the radical word, impossible because that image is sofic.  Hence the only
remaining TRUE obstruction is uniformity in growing dimensions:

`C_fd(d)<infinity for every d`, but `sup_d C_fd(d)=infinity`.

This removes exact finite-stage searches, nonlinear fixed-dimensional
deformations, and singular projective solution strata from the live gate.

The matrix side can now be made irreducible as well; see
`TRUE_IRREDUCIBLE_DOMINATION_REDUCTION.md`.  With
`delta_sigma(g)=1-Re tr(sigma(g))`, conjugate-double decomposition and
trivial-block dilution give the exact equality

`C_fd=sup_(sigma irreducible) delta_sigma(w)/sum_R delta_sigma(r)`.

The restricted supremum over irreducibles of degree at most `D` is finite
for every `D`, again by jet truncation.  Even arbitrary total dimension and
multiplicity are harmless if all irreducible blocks have bounded degree.
Thus the live TRUE comparison is now between transitive finite permutation
representations and irreducible unitary representations whose degrees tend
to infinity; reducible mixtures and multiplicity growth are not part of the
gap.

The induced finite-image part of that growing-degree comparison is now
sharply controlled; see `TRUE_INDUCED_IDENTITY_GAP_DOMINATION.md`.  If
`sigma=Ind_H^F(tau)` and `tau` has finite image, its normalized character
defect is sandwiched against the moved fraction of the finite coset action
`F/ker(tau)`:

`min(1,eta(tau)) d_(F/ker(tau))(g) <= delta_sigma(g)`
`                                      <= 2 d_(F/ker(tau))(g)`,

where `eta(tau)` is the least normalized trace defect of a nonidentity
inducing block.  The classical radical inequality therefore transfers with
loss `2/min(1,eta(tau))`, independently of `[F:H]`.  In particular,
finite-image monomial irreducibles of bounded phase exponent, and more
generally induced finite-image blocks of bounded dimension and exponent,
cannot obstruct TRUE.  Any induced finite-image obstruction must have
identity gap tending to zero; growing coset degree alone is harmless.

The complementary unbounded-phase sector is now connected exactly to the
carry/discriminant program on every exact finite quotient chart; see
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md`.  Integral fillings of the
lifted radical loops give an integer factorization `B_(w,X)=Z_X A_X` from
relator holonomy to word holonomy.  The optimal additive monomial
domination constant is the marked torus Lipschitz ratio of this factor map,
and the optimal chordal/character constant is universally equivalent to its
square.  Its exact formula `(ECM31)` has the paired-discriminant lower
envelope as denominator and the canonical radical filling pairings as
numerator.  Hence bounded marked ratios rule out all phase orders on exact
charts.  The remaining monomial overlap is unbounded phase order on
nonexact permutation charts, plus possible growth of the marked ratios over
exact charts.

Full circle repair is a sufficient uniform bound for every marked radical
word: `(ECM24b)-(ECM24c)` give
`Lambda_(w,X)<=|w| C_circ(A_X)<=|w|Theta(A_X)/sigma_+(A_X)` and the
corresponding character constant is at most `pi^2/4` times its square.
Therefore the exact property-`(T)` Hodge gap plus a uniform integral-carry
bound closes arbitrary phase orders on all exact charts.  A marked ratio can
still remain bounded when full circle repair does not, so `(ECM31)` is the
sharper word-specific target.

The exact/nonexact chart transition now has a quantitative composition
theorem; see `TRUE_STABLE_BASE_CARRY_TRANSFER.md`.  Keep the original phase
labels while replacing the permutation part by an exact `P`-action.  If `h`
is the generator Hamming exactification cost, `E_R` is the relator HS defect,
and `C_circ` is the resulting exact-chart repair constant, then `(SBC17)`
gives

`||U(w)-1||_2 <= |w|sqrt(2h)`
` +(pi/2)|w|C_circ(E_R+sqrt(2h)L_R)`.

Hence sequencewise permutation exactification plus uniform carry repair
kills every monomial radical witness, with no bound on phase order.  In
particular, permutation stability of the presentation together with a
uniform exact-chart carry bound closes the entire monomial branch.  This
proves that base repair and phase repair have no hidden third compatibility
loss; what remains is to establish them for the relevant charts, and to
obtain a common Cartan/monomialization for arbitrary matrix characters.
The conclusion is unchanged under flexible exactification by adding or
removing `o(|X|)` points: extend both models to a common set with trivial
actions and phases, apply `(SBC17)`, and use the asymptotically unit dimension
ratio (`(SBC29a)-(SBC29b)`).

On the amplified FALSE lane, full base transfer reduces the modular
holonomy search to a fixed-rank dual norm; see
`FALSE_BASE_HOLONOMY_DUAL_NORM.md`.  For a fixed integral basis of the base
cycle lattice, center its `k` radical-transgression values modulo `q` into a
vector `c in Z^k`.  The optimal ratio
`sup_(v!=0) H_q(Hol(Jv))/||v||` has an exact finite shortest-representative
formula and is bounded above and below by fixed basis constants times
`||c||`.  Hence unbounded centered basis holonomy already supplies one fixed
primitive cycle to the amplified transfer-holonomy certificate and proves
FALSE.  Computationally, on full-transfer charts it is enough to solve the
`k` basis right-hand sides and watch one fixed-dimensional output vector;
searching over all base cycles is unnecessary.  Full transfer itself remains
a substantive unproved hypothesis for the candidate chart families.

The degree congruence gives that fixed-rank character an exact arithmetic
normal form; see `FALSE_FULL_TRANSFER_TORSION_NORMAL_FORM.md`.  If a regular
cover has degree `n`, modulus `q`, `g=gcd(n,q)`, and the whole base cycle
lattice transfers, then `e=q/g` divides the fixed Gram content of that
lattice.  Radical holonomy decomposes uniquely as
`Hol(Jv)=<v,z_0>+e psi(v) mod q` for a character
`psi:K_1->Z/gZ`.  Centered basis holonomy differs in norm from `e` times the
centered coordinate vector of `psi` by at most the fixed base-filling norm.
Since `e` ranges over finitely many divisors, the amplified FALSE condition
is exactly unbounded growth of this fixed-rank degree-torsion character.
Thus all full-transfer growth is confined to the common nonsemisimple part
of cover degree and modulus; the coprime sector is rigorously inert.

That torsion character itself is now identified with one paired integral
class; see `FALSE_TRANSFERRED_FILLING_PAIRING_FORMULA.md`.  Transfer an
integral filling of a lifted radical loop to the base and subtract a fixed
base filling.  Its class `kappa_(w,X) in K_1/S(K_X)` is independent of all
choices.  For every transferable `(v,q)`,
`Hol(Jv)=<v,z_0>+<v,kappa_(w,X)> mod q`; under full transfer the second term
is the mod-`q` Gram pairing on the transfer quotient.  In a fixed basis the
whole holonomy vector is exactly `f+Gm_X mod q`, and the degree-torsion
vector is `(G/e)m_X mod g`.  This removes the modular phase solve from the
marked numerator and identifies the remaining nonlinear obstruction with a
single relative filling class in a finite paired lattice quotient.
Bounded quotient torsion is already decisive: if one fixed primitive cycle
detects a nonzero relative filling class modulo unbounded transferable
moduli, and those classes have order bounded by `E`, their centered
holonomies are at least `q/E-O(1)`.  The amplified certificate then proves
FALSE.  In particular, finite exponent of `H_2(H,Z)` reduces the construction
to persistence of a nonzero paired class; growing torsion order is not
needed.

Rayleigh selection cannot reduce that comparison to individual vector
states; see `TRUE_ONE_ROOT_VECTOR_STATE_NO_GO.md`.  Although every normalized
trace ratio has a vector-state ratio at least as large, every quotient
`F/N`—with no soficity assumption—has exact finite permutation models at one
distinguished root on every finite word window.  Complete the generator
partial bijections on a finite Schreier ball.  The resulting root coefficient
equals `1_N` exactly on the window.  Hence vector-state/Fell approximation is
vacuous here: TRUE is the passage from one good root to a density-one set of
good roots, and the irreducible reduction must retain normalized trace or
macroscopic rank.

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

The principal skew-product reformulation gives a direct relation-theoretic
proof for every countable-range circle cocycle.  If `lambda` is cohomologous
into a countable subgroup `A<T`, then `R_Q(lambda)` is a subrelation of
`R_Q times S_A`, where `S_A` is the hyperfinite translation relation of
`A action T`.  Product and subgroupoid permanence make the skew product
sofic, and principalization then makes `Gamma` sofic (`(HPK9cc)-(HPK9cf)`).
The same bounded-phase conclusion was already implicit in Theorem 3A, since
countable range of `lambda=b^m` forces countable range of `b`.  Thus finite
generation, property `(T)`, and Pruefer scalar divisibility are irrelevant in
the countable-range case.  A surviving bounded-exponent residue must have no
countable-range gauge on any finite-index restriction.

The exact countable-range hypothesis can now be weakened to a closure
hypothesis.  For the essentially-free quotient action, if circle cocycles
`lambda_n` with countable-range gauges converge in measure, generator by
generator, to `lambda`, then their sofic skew-product relations converge in
all finite labelled statistics to `R_Q(lambda)`.  Essential freeness keeps
every nontrivial-word fixed-point statistic identically zero, avoiding the
rotation discontinuity in the property-MD no-go.  Hence `R_Q(lambda)` and
then `Gamma` are sofic (`(HPK9cg)-(HPK9ck)`).  The surviving target is now
outside the convergence-in-measure closure of all countable-reducible
cocycles, a sharper condition than uncountable essential range.

Package that boundary as
`H^1_cr=Z^1/closure(Z^1_cr)`, where `Z^1_cr` consists of cocycles
cohomologous into countable circle subgroups.  It is a genuine quotient
because `Z^1_cr` is a subgroup, and `closure(B^1)` lies inside its kernel.
Thus a live phase residue has nonzero `H^1_cr` class on every relevant
finite-index restriction.  Do **not** call `lambda=b^m` a special density
hypothesis: every circle cocycle has a measurable pointwise `m`th root `b`
with `delta b` in `mu_m`.  Any further TRUE argument must use compatibility
of the particular root/curvature with the evaluated extension cocycle and
the Haar character field, not merely the power equation (`(HPK9cl)-
(HPK9cq)`, `(TWT32)-(TWT38)`).

Calibration: Bezuglyi--Sanadhya's density of coboundaries for hyperfinite
Borel actions gives `H^1_cr=0` there (`(HPK9cr)`, `(TWT39)`), recovering the
amenable endpoint.  No such density result is known for arbitrary principal
sofic relations.

Every circle skew product has a canonical vertical wreath envelope.  The
fiber rotations `V_(r,s)(x,t)=(x,lambda_r(sx)t)` generate a hyperfinite
relation normalized by the lifted base action, and together they form an
action of the abstractly sofic restricted wreath product
`(directSum_Q Z) wr Q`.  The skew action lies inside this envelope
(`(HPK9cs)-(HPK9cx)`, `(TWT40)-(TWT45)`).  This does not close the gate:
soficity of the abstract wreath product does not make this particular action
sofic.  Coordinatewise torsion quantization respects the base shift but can
destroy vertical kernel relations, including the cocycle identity; a tiny
carry moves the whole phase fiber.  The live statement is soficity of this
specific wreath action, equivalently the relation-preserving completion
`(HPK18)`.

Universalize the same gate via the projective full shift.  Every cocycle has
the equivariant orbit-configuration factor
`Phi_lambda:X->P_Q=T^Q/T`, and is the pullback of
`c_q([f])=f(q)/f(1)`.  The skew action on `X times T` is exactly the
relatively-Haar fiber product
`{(x,f):[f]=Phi_lambda(x)}` with the shift on `T^Q`
(`(HPK9cy)-(HPK9dh)`, `(TWT46)-(TWT51)`).  This quotient is exactly Popa's
factor map.  Austin's property-`(T)` examples show that universal
model-surjectivity is false: good projective models may live in nonzero
finite-graph cohomology sectors a uniform distance from every global vertex
potential.  This does not obstruct finite-phase completion: Austin's
bad models are already exact circle cocycles, and torsion points are dense in
the exact-cocycle subgroup of every finite chart.  The live theorem is
therefore different, not merely weaker: select **one** model sequence,
compatible with the given base colors and relatively-Haar joining, for which
vanishing raw cocycle defect forces vanishing distance to the exact cocycle
locus.  Torsion density then supplies finite-phase equality away from `o(1)`
vertices.  This is exactly the qualitative cocycle-stability gate
`(CS1)--(CS8)`, not a choice of cohomology sector.  The Popa audit is in
`docs/POPA_FACTOR_MODEL_LIFTING.md`.  Product permanence still uses the
wrong, independent joining.

Complete-simplex unfolding does not bypass this gate.  On `V times F`, the
label potentials make the phase transitions an exact coboundary and permit
exact torsion rounding, but completing the partial translations
`q |-> gq` costs `|gF triangle F|/(2|F|)`.  This vanishes along an
exhaustion exactly in the Følner/amenable case.  Identifying the local copies
through `(v,q) |-> sigma_q(v)` removes that boundary only if the rounded
phases agree on overlaps, which is `(CS1)` again.  The proof and quantitative
boundary estimate are in `docs/PHASE_UNFOLDING_AMENABILITY_BARRIER.md`.

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

There is a second exact endpoint which does not demand splitting.  The
torsion twist `Sigma_omega=mu_infty times_omega R_Q` contains `Gamma` in its
full group via the bisections `x |-> (a_k(x),q,x)`.  Essential freeness and
the Haar law give every nonidentity bisection positive metric length, so
soficity of `Sigma_omega` would imply soficity of `Gamma` after product
amplification.  This is not automatic from soficity of `R_Q`: universal
finite-twist permanence would already settle the open finite-central-kernel
extension problem.  The two live alternatives are therefore torsion splitting
or direct sofic approximation of this special evaluated-extension twist.
There is an intermediate virtual criterion: it is enough for the torsion
class to vanish on a finite-index subrelation.  Its full preimage retains all
torsion isotropy, is a sofic product groupoid by Cordeiro's product theorem,
and has finite index in the whole twist; Cordeiro induction then applies
noncircularly.  In particular Kida's treeable cohomology vanishing shows that
a finite-index treeable subrelation closes the phase gate.
For bounded-exponent kernels, character-rigid quotient actions also close:
every character of a finitely generated `Q` becomes `m`-divisible on the
finite-index preimage of `m Z^r directSum 0<Q_ab`.  Thus the Popa carry
calibration is globally nonsplit but virtually split.  The remaining
bounded-exponent obstruction must stay non-character-like under every
finite-index restriction.
More generally, if `lambda` is cohomologous to a cocycle taking values in
any finitely generated subgroup `A<T`, restrict to the finite-index kernel
of `A -> A/(m Z^d directSum 0)` and divide the remaining free coordinates by
`m`.  Hence a surviving phase class must have essentially infinitely
generated scalar range after every gauge and every finite-index restriction.
For an ergodic property-`(T)` quotient action, even countable range closes:
the skew-product representation on `L^2(X,ell^2(A/A_0))` turns a large
finite range truncation into an almost invariant vector, and its invariant
repair has a unique dominant coordinate which gauges the cocycle into
finitely generated `A_0`.  The scalar method is sharp at Pruefer
`p`-torsion, where multiplication by `p` has no right inverse and there are
no proper finite-index subgroups.
Mackey's compact-cocycle reduction sharpens the invariant boundary further:
on every finite-index ergodic restriction, a proper Mackey subgroup of the
circle is finite and therefore closes by the virtual finitely-generated
range theorem.  Any surviving residue must have full circle Mackey range on
all such restrictions.  Moreover `lambda=b^m` cannot itself be
torsion-valued: that would force `b` to be torsion-valued and give the
torsion primitive immediately.  Pruefer behavior can arise only after a
genuinely non-torsion transfer.
The unsplit Bockstein has a principal endpoint as well.  Its fixed-alphabet
root groupoid acts freely on `X times T`; the resulting relation is exactly
the finite amplification `R_Q(lambda) times (mu_m)^2`.  The action embeds
the root groupoid full semigroup trace-preservingly into this relation.
Hence soficity of the ordinary circle skew-product relation `R_Q(lambda)`
already proves soficity of `Gamma`.  In the Mackey-full case this skew
product is ergodic.  Universal compact-skew-product permanence remains
unavailable and would cross the finite-central-kernel boundary.

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

The collaborator's universal cyclic-module candidate and exact coinduced
parity model are the same analytic target.  Fourier transform on
`A_univ` identifies the signed coinduced crossed product with the normalized
`z=-1` central corner `p_-L(E_univ)`; at the reduced C-star level,
`A_(G,s)=p_-C_r^*(E_univ)`.  The `z=+1` corner is the ordinary wreath
quotient.  Thus the FALSE gate is exactly MF/Connes embeddability of one
explicit negative central corner, not a choice between two representations.
The proof and the precise non-permanence warning are in
`docs/COINDUCED_NEGATIVE_CENTRAL_CORNER.md`.

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

## 5. Two-chart atlas computation  [FIRST SIGNAL]

The MSI experiment in `experiments/atlas_two_chart_results.md` translates 54
exact Steinberg/Leavitt relations through the explicit `A8*A8` atlas and
tests all 648 centrality constraints obtained from twelve chart generators.
Exact `F_2` Leavitt reduction validates every source relation.  At
multiplicities `k=1,2,4`, worst-tail optimization reduces the maximum
normalized-HS defect only

`1.27256 -> 1.24958 -> 1.23908`.

The gain is genuine but slow.  Exhausting all 40,320 automorphisms of `A8`
finds no exact classical alignment: the best inner alignment satisfies
`42/54` source relations and the best outer alignment `20/54`.  Thus the
subsystem has nonclassical multiplicity daylight but no near-solution.
Next: extract the full finite normal-relator list before larger blind runs;
in parallel, target the persistent scalar Steinberg/Cuntz branch for a
dimension-free trace or SOS inequality.

The natural-eight-point red-team in
`experiments/atlas_one_involution_results.md` adds the commuting-Boolean
geometry from the current one-involution FALSE endpoint.  GAP's exceptional
isomorphism `GL_4(F_2) ~= A8` makes a chart transvection four disjoint
2-cycles, so a diagonal involution can be chosen exactly antipodal.  At the
best classical inner alignment, all 78 conjugate-commutator tests vanish
exactly while the 648 atlas constraints have RMS defect `0.46811943`.
Multiplicity two lowers this only to `0.46792161`, with orbit RMS
`0.00567036`; the atlas operator maximum remains `2`.  Thus the finite
Boolean sector does not cause the atlas floor, but the observed improvement
is merely local perturbative daylight.  Do not scale this blind.  The same
scalar `e/E` Steinberg--Cuntz branch remains the dual/SOS target.

On the direct FALSE lane, Corollary 10 of
`FALSE_MACKEY_SPLIT_COCYCLE.md` lowers the final one-involution endpoint from
operator norm to normalized Hilbert--Schmidt norm: finite telescoping of the
unitary products and commuting lamp factors passes directly to the tracial
ultraproduct.  Operator norm remains relevant only for the stronger MF
statement.  The coinduced parity model already realizes antipodality and all
commuting conjugates exactly in a finite crossed product, so the direct
matrix problem is now approximation of that explicit crossed product while
retaining its radical sign, not construction of the infinite-dimensional
parity action.

`FALSE_RF_VERTEX_HS_MATCHING_NO_GO.md` closes the most immediate use of the
new residually finite vertex decomposition.  For the special Kun--Thom fold
word `s=i_2(h)i_1(h)^(-1)`, property `(T)` implies that any two honest
finite-dimensional representations of the RF vertices whose restrictions
become normalized-HS compatible on the common edge satisfy `s->1`.
Asymptotic amalgam gluing and `z=[v,s]` then force `z->1`; equivalently the
negative spectral rank is `o(d)`.  Thus even tracial matching of arbitrary
exact RF vertex models cannot solve the FALSE endpoint.  At least one vertex
must already be represented by a genuinely nonliftable HS
almost-representation.

The one-orbit clutching refinement does not evade this no-go by implementing
the lamp shear exactly.  The same note proves the quantitative bound: if
exact vertex representations agree on `A_s` and the central involution has
negative relative rank `delta`, their mismatch on a fixed Kazhdan set of
`Gamma` is at least `(kappa/2)sqrt(delta)`.  In particular an exact global
Boolean flip with `z=-1` leaves a dimension-independent edge defect of at
least `kappa/2`.

The first cohomological-code spectrum calibration is in
`experiments/phase_code_spectrum_results.md`.  Exact locally free `F_2`
Schreier charts can have a two-block bottleneck with only two cross-half
generator edges.  Their binary half-word has check defect `1/n` but distance
`1/2` from the degree-zero cocycle code, while the first positive incidence
singular value is asymptotic to `2/sqrt(n)`.  MSI sparse spectra through
`n=4096` reproduce this law; random Schreier controls retain gap about
`0.72`.  Thus neither soficity, essential freeness, nor local statistics
alone can give the uniform repair spectrum suggested by `(PFL11)`.  A TRUE
decoder must select expanding/cosystolic charts or exploit the prescribed
relatively-Haar joining; arbitrary-chart spectral mining is a dead route.

The first genuine degree-one selected-chart computation is in
`experiments/sl3_degree_one_spectrum_results.md`.  For the fixed six-root,
13-relator presentation of `SL_3(Z)` acting on `F_p^3-{0}`, sparse MSI runs
through `p=37` give coexact degree-one singular bottoms between `0.7678` and
`1`, on complexes ranging from 156 to 303,912 edges.  This is evidence for
a linear repair estimate on these selected property-`(T)` charts, not a
uniform-gap proof and not yet circle/torsion repair.  More importantly, the
lowest modes split exactly under the commuting scalar `F_p^*` action: the
`p=23` anomaly is wholly in the quadratic-character block, while the `p=37`
mode is wholly scalar-invariant.  Stop extending the raw prime table.  The
scalar-character Fourier reduction is now implemented and validated in
`experiments/sl3_character_block_spectrum.py`; at `p=37` it reduces 303,912
edge coordinates to 8,442 per block and reproduces the full minimum to
`1e-14`.  An all-character pass shows that primitive, quadratic, and trivial
characters can each be the winning sector.  Any certificate search therefore
had to control every character order rather than extrapolate one block.

That certificate search has succeeded in a stronger universal form; see
`TRUE_SL3_HODGE_SOS.md`.  A 102-by-132 rational group-ring factor and an
exact coefficient residual prove

`Delta_1 >= 14164556740143/5000000000000000 I`

for the fixed `SL_3(Z)` presentation in every unitary representation.  This
makes the qualitative property-`(T)` result in
`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` explicit and gives

`dist(a,Z^1) <18.789 ||d1 a||`.

The real-linear selected-chart gate is therefore closed.  Do not spend more
compute on its character blocks.  The live obstruction is integral and
nonlinear: lift circle phases through integer carries, retain the
finite-order cohomology class, and turn `L2` repair into Hamming deletion.
On the FALSE side the same issue asks whether varying torsion curvature can
evade real repair and furnish the genuinely nonliftable projective sector.

`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md`, Proposition 4, also closes the
tempting universal generalized-inverse search.  For any infinite one-ended
finitely presented group, `DBD=D` over `Z[G]` would split `ker D=im d0`;
augmentation makes that impossible.  In particular it cannot hold for
`SL_3(Z)`.  The surviving compute target is chart-dependent: measure or
construct the finite carry lattice `ran(d1_V) intersect Z^cells` and its
transversality, not one universal integral group-ring splitting.

The first such audit is in `experiments/sl3_carry_results.md`.  Basis
leverage through `p=37`, exhaustive two-cell searches, torsion-cell LLL at
`p=3,5`, and a full-cell LLL pass at `p=3` find no divergent carry.  The
strongest class is always the fixed-axis CRW torsion cell and stabilizes at
`Theta>=4.543096`.  Exact Smith arithmetic gives saturation quotient `C_3`
at `p=3`; at `p=5`, three cold-verifiable maximal minors have determinant
gcd one, proving that the relator image is saturated.  This is positive
signal for bounded carry transversality, not an upper bound.  The next
solver must synthesize a uniformly bounded chart-dependent integral
reduction operator or exhibit a long carry with projected norm tending to
zero.  Dense Smith forms are superseded by sparse modular selection and
exact determinant/gcd certificates.

The saturation computation is not the terminal invariant.
`INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` proves that `Theta` is governed by
the discriminant gluing of the primitive cycle lattice
`ker(d1^T) intersect Z^cells`; saturation of `im(d1)` neither bounds nor
forces it.  The next autonomous solver must therefore construct the cycle
Gram discriminant module and certify the paired closest-vector radii, using
the scalar/chart symmetries to avoid unrestricted high-dimensional CVP.

The first exact cycle computation confirms that requirement.  At `p=3`,
the primitive cycle lattice has rank 207 and a 296-bit discriminant with 13
nonunit Smith factors; the fixed-axis cell alone has enormous class order
but squared distortion only `20.612266...`.  Exhaustive class enumeration
and class-order heuristics are therefore both dead.  Exact combined-map
minor certificates also prove full constant-cycle transfer at `p=3,5`, in
agreement with the Schur-multiplier theorem.  Continue only in genuinely
new-cover symmetry sectors of the cycle discriminant module.

The cover Hopf quotient now makes "new-cover" precise.  For `X=G/H`, if
`Sigma_X` is the subgroup of the cycle lattice represented by lifted
spheres, then

`K_X/Sigma_X ~= H_2(H,Z)`.

Because `SL_3(Z)` is of type `F_infinity`, `Sigma_X` is generated by the
lifts of finitely many bounded spherical templates.  Thus the full carry
gate has two exact parts: norm-controlled integral decoding in that local
spherical lattice, and discriminant control for the varying stabilizer
Schur multipliers.  Finiteness of `H_2(SL_3(Z),Z)` closes neither part; it
only closed the already-separated transfer of base cycles.

The scalar-involution audit makes those sectors explicit.  The integral
plus/minus split has index `2^103` at `p=3`; its gluing codes are
`[169,103]` and `[806,495]` at `p=3,5`.  They contain many weight-one words,
so cosystolic expansion is false, but weight-at-most-four words generate
only ranks `61` and `157`, so a bounded local-generator proof also fails at
the first tested bound.  The next TRUE solver must price high-support
binary gluing in the sector Gram norms.  Do not infer distortion from code
dimension, minimum weight, or discriminant-class order alone.

The exact involution-overlattice formula performs the needed algebraic
compression.  If `K_0=K_+ directSum K_-` and `C=K/K_0` is the binary gluing
code, then

`D_K ~= C^perp/C`,

and each shortest discriminant radius is a weighted nearest-code distance,
the sum of its two sector Gram distances minimized over `C`.  Odd-primary
torsion splits completely between the two sectors; only the two-primary
part is coupled by the code.  A codeword of support `w` has prequotient
squared sector cost at least `w/2` in each sector.  Thus the live invariant
is the nearest-code radius in the sector metrics, not whether high-support
codewords admit a bounded-support generating set.

The gluing code itself is the homology image for the scalar two-cover:

`C=im(H_2(P_H,Z)->H_2(P_J,F_2))`.

The long exact sequence of the integral trivial/sign local systems says it
is also the kernel of one connecting map.  After quotienting the spherical
subgroup, its exact nonspherical part is

`im(H_2(H,Z)->H_2(J,F_2))`.

Thus low-weight codewords may be merely lifted bounded spheres.  Separate
those local templates before interpreting the measured weight distribution;
the genuinely global nearest-code obstruction is a stabilizer-homology
image, not an arbitrary binary code.

For a selected `SL_3(Z)` chart family, the scalar code can be removed
entirely: use the exact actions on `P^2(F_p)` instead of on
`F_p^3 minus {0}`.  Every fixed nonidentity integral matrix is nonscalar
modulo all but finitely many primes and then fixes at most `p+2` of the
`p^2+p+1` projective points, so this family is still asymptotically free.
The universal Hodge SOS applies unchanged.  Its carry lattice is the
trivial scalar-character sector, with no scalar gluing.  This does not
control that sector's odd discriminant or stabilizer homology, but a proof
which needs only one selected exact family should not solve the strictly
harder all-character gluing problem first.

The first exact projective-chart audit is now in
`experiments/sl3_projective_carry_results.md`.  For the point stabilizers at
`p=3,5,7`, exact Shapiro boundary complexes give rational `H_2=0` and
integral groups `C_2^3,C_2^3,C_2^4`.  The small-level boundary ranks follow
`3n+1` and `7n-1` for `n=p^2+p+1`.  This is a valuable calibration, not a
uniform theorem: prime-level cuspidal cohomology gives nonzero rational
`H_2` at later levels.  Thus the live program must control both numerator
growth on the acyclic charts and the metric harmonic lattice on the
non-acyclic charts.

The first non-acyclic chart is now computed exactly at `p=53`.  The Shapiro
complex has rational `H_2` of dimension two: its `F_101` ranks give the
upper bound two, matching the two-dimensional cuspidal lower bound of
Ash--Yasaki.  A sparse real Hodge solve isolates the same two-plane with a
gap of `0.19377` to the next eigenvalue, and 64.15 percent of its leverage
lies in one five-term degree-two cell orbit.  The live metric calculation is
therefore an exact rank-two lattice lift/regulator problem, not another
homology-dimension sweep.  See
`experiments/sl3_projective_carry_results.md`.

`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` now gives the exact optimal
nonlinear repair constant, not only a comparison through `Theta`.  It is
the quotient of the ellipsoidal distance to the saturated range lattice by
the lower envelope of the finitely many paired discriminant wells.  This
sharpens the old constants to
`sqrt(Theta^2-1)/||A|| <= C_circ <= Theta/sigma_+`.  More importantly for
the cuspidal chart, it proves
`Q^#=H intersect (Z^m+W)` and embeds
`Q^#/(H intersect Z^m)` into the paired range discriminant.  Hence the
`p=53` regulator, dual systole, and all sub-spherical-threshold paired
classes can be recovered from a two-variable rational lattice pullback;
constructing the full rank-20,000-plus integral cycle kernel is unnecessary.

`TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md` now converts the remaining
harmonic numerator into an integral decoder.  The spherical annihilator
lattice fits into the exact sequence
`0->L->M_Sigma->Q^#->0`, and the glued range radius is exactly the extra
Pythagorean norm paid by an ambient integer lift.  Its nonlinear lift
distortion is equivalent, in harmonic rank `r`, to the least norm of a
`Z`-linear section up to a rank-only lattice-reduction constant.  For the
rank-two `p=53` chart the factor is `4/sqrt(3)`, and any two integral basis
lifts give a complete bound through a `2 x 2` generalized eigenvalue.  The
same note now gives the exact regulator balance
`Reg(Q^#)=Reg(S_sat)/Reg(L)`.  Thus the harmonic regulator and the
determinant lower bound
`kappa^2>=(3/16)Reg(L)/Reg(S_sat)` at rank two require only saturated
boundary/coboundary determinants and Smith indices, not an exact harmonic
basis.  The basis is still needed for shape, dual systole, and an upper
bound.  The next exact computation should therefore first evaluate this
determinant ratio, then solve two affine integer lift problems; it should
not enumerate the full discriminant group.

On the FALSE side, the paired carry energy now has the coordinate-order
formula in `FALSE_CARRY_MEAN_SUPPORT_FORMULA.md`: its uniform subgroup mean
is a sum of `nu(o_j)` over ambient carry characters, with every nontrivial
coordinate contributing between `2/27` and `1/8`.  This immediately kills
uniform mean pruning for nonzero deck-invariant codes in regular covers of
a fixed presentation, since their support contains a full deck orbit; see
`FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.  The exact nonuniform replacement
is `FALSE_BERNOULLI_CARRY_INCIDENCE.md`: in a two-torsion parametrization,
FALSE follows if the maximum carry-row degree `a_n` is negligible compared
with the marked-word row degree `b_n` on a positive fraction of word
coordinates.  The live finite search is therefore an incidence-separation
calculation, not a uniform discriminant average.

Bounded spherical templates already localize every vanishing denominator.
If their maximum norm is `B`, then a dual cycle `u` with `||u||<1/B` pairs
by an integer of magnitude less than one with every template, hence is
orthogonal to the whole spherical lattice.  Its real component therefore
lies in `H_2(H,R)`.  In particular, when a chart stabilizer is rationally
two-acyclic, every nonzero discriminant class has cycle radius at least
`1/B`, uniformly.  This does not bound the paired range radius: the two
remaining failure modes are now denominator collapse inside stabilizer
homology and numerator growth with denominator bounded below.

This also fixes the architecture of the autonomous FALSE solver.  It must
not enumerate exact RF vertex representations and hope that ILP plus an
intertwiner retains the radical sign: `FALSE_RF_VERTEX_HS_MATCHING_NO_GO.md`
proves that every such asymptotically compatible exact-vertex sequence kills
the sign.  The primal variables must include a genuinely nonliftable
normalized-HS almost-representation inside at least one vertex.  Exact RF
models may serve as controls or auxiliary blocks, never as the complete
projective-sector ansatz.

The radius-ten atlas boundary appeared to have a smaller structured ansatz.  With
`H=GL_3(F_2)<A8`, left-coset coordinates give
`ell^2(A8)=ell^2(H) tensor C^120`; relative unitaries
`U_V=(I_H tensor V)J`, `V in U(120)`, preserve exact commutation with the
whole left `H`.  The exact word-support audit kills it: 210 of the 234
failing words lie in `H*H`, forcing a regular commutator defect `sqrt(2)`
for every `V`.  Do not launch this `U(120)` optimization.  Any successful
deformation must break exact `H`-equivariance as well as leave the monomial
category; a dense `U(20160)` search is still not justified.

There is a viable smaller replacement.  Among the 30 point/hyperplane
stabilizers `M` of order 1,344, 18 contain none of the 234 boundary words in
both factors.  For these index-15 subgroups, search
`U_V=(I_(ell^2 M) tensor V)J` with only `V in U(15)`.  This stays in the
full 20,160-dimensional regular sector but evades the exact support no-go.
Implement traces through induced/coset coordinates; do not materialize
20,160-square matrices.

That implicit implementation is now live.  Two bounded orthogonal searches
from rotation scales `0.02` and `0.20` descended toward, but not below, the
balanced tensor-flip loss one.  Stop multiseed optimization.  Compute the
exact induced-coordinate Hessian at `V=I`; a rational positive certificate
would establish local rigidity of every surviving index-15 stabilizer
ansatz, while a negative eigendirection would give a principled continuation
seed.

The exact Clifford word has now been closed algebraically.  Abstract
centrality first gives `c_01=c_02=c_12=q^2` and `q^4=1`.  The local generators
admit the common six-leaf scalar refinement

`D=(000,001,010,011,10,11)`, `G_D ~= GL_6(F_2)`.

This group is superperfect, so its unique lift to the central atlas cover
shows that the common commutator is trivial and `q^2=1`.  Uniformly refining
the second chart gives a superperfect `GL_8(F_2)` chart.  Its overlap with the
six-leaf chart contains the common perfect subgroup

`GL({000,001,10,11},F_2) ~= GL_4(F_2) ~= A8`,

and the element `b` lies in this overlap.  Uniqueness over the two
superperfect charts and agreement over the perfect overlap force their lifts
of `b` to coincide.  Hence the residual discrepancy is trivial and `q=1` in
`P/[P,R]`.  The entire Clifford block is therefore a proved no-go; do not
optimize either its `q=-i` or `q=-1` sector further.  A new FALSE witness must
use another cross-chart relation that survives this perfect-overlap test.
The five-term sequence alone only makes the central kernel a quotient of
`H_2(Q,Z)`, because `H_2(A8*A8,Z)=C2 directSum C2`; it is not automatically
the whole Schur multiplier.  Full proof:
`docs/FALSE_CLIFFORD_TORSION_GATE.md`.

The 64-dimensional block is now executable.  It validates the Pauli
identities below `5.4e-14` and centralizes 19 of the 234 radius-ten boundary
words, all inside one 25-word `(1,b)` projection class.  Six words with the
same projections remain, showing computationally that projection pairs do
not determine compatibility.  A 20-step search over the exact
Clifford-preserving `U(32) x U(32)` manifold lowers RMS slightly but leaves
maximum defect exactly `2`.  The perfect-overlap bridge decides the algebraic
survival problem negatively, so stop numerical refinement of this branch.

The perfect-overlap mechanism has now been run on the entire first boundary.
Among its 234 tensor-flip failures, 178 are proved trivial in `R/[P,R]` by
common superperfect charts of sizes 6, 8, or 10.  The remaining 56 words fall
into only eight projection classes.  They are not merely beyond the search
cutoff: their matrix-support equalities turn the two common-refinement suffix
cardinality equations into positive contradictions, so none can lie in one
scalar chart at any depth.  Their two factor subgroups have orders 4 and 8.
Use one representative from each class for exact central-phase/character
analysis before launching another unitary optimizer.  Full criterion and
counts: `docs/FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md`.

The first of those eight incompatible classes already has an exact phase
seed.  With `a=I+E_10`, `b=I+E_01`, `c=I+E_12`, and
`d=I+E_01+E_12=cb`, the relation

`r=a_2 b_1 c_2 b_1 a_2 b_1 c_2 d_1`

is the identity in the Leavitt group but forces a suffix code to equal its
own proper refinement, so no single scalar chart contains its letters.  Its
local factor groups are `V4` and `D8`.  The Pauli assignment
`b->X`, `c->Z`, `a_2,c_2->cos(pi/8)X+sin(pi/8)Y` gives `r->i`.
Inside the 64-dimensional `(5,2,1)` `A8` irrep, exact restriction characters
give sixteen copies of this two-dimensional block.  Two honest `A8` charts
can therefore be aligned so that `r` has spectrum
`i^[32],1^[16],(-1)^[16]`, commutes with the local `D8` and `V4`, and has
normalized distance squared `2` from one.  It does not yet centralize the
full charts or prove that `r` survives in `R/[P,R]`.  This is now the first
live self-similarity phase seed; full calculation:
`docs/FALSE_SELF_SIMILARITY_PHASE_SEED.md`.

The 64-dimensional seed is now executable rather than character-theoretic
only. Exhausting all six complementary `D8`-character matchings reproduces
the spectrum `i^[32],1^[16],(-1)^[16]`, trace `i/2`, and exact local
centrality to below `1.3e-14`. Every matching nevertheless has full-chart
maximum commutator defect exactly `5/4`; the best twelve-generator RMS is
`0.8228507358`. Thus discrete complement reassignment is exhausted. Continue
only with a genuinely deformable relative-unitary or nonorthogonally coupled
ansatz that trades full-chart centrality against macroscopic phase. Exact
construction and diagnostics: `experiments/atlas_self_similarity_block.py`
and `docs/FALSE_SELF_SIMILARITY_PHASE_SEED.md`.

The full relative-unitary continuation is now the leading FALSE signal.
Starting from the lowest-RMS exact complement, worst-tail Cayley descent in
`U(64)` reduced the maximum of all twelve chart-centrality defects from
`1.25` to `0.0295801`, while moving the normalized relation trace from `i/2`
to `2.4e-9 + 0.9998817 i`. The retained state has
`||r-iI||_2=0.0153837` and operator-norm error `0.0423631`; its alignment is
dense and lies normalized-HS distance `0.78677` from the seed. Stop broad
weight/seed sweeps. The live exact target is now the fixed-dimensional
equation `r(U)=iI_64`: compute its tangent rank, apply a local exact/Newton
solver, and recognize an algebraic block model. Solving it certifies the
one-relator central phase but does not yet prove survival in `R/[P,R]`, where
commutators involving all other Leavitt relators also matter. The
multi-relator central-kernel and negative-corner gates remain. Full record:
`experiments/atlas_self_similarity_refine_results.md`.

Local solvers sharpen that signal but also expose the next mathematical gate.
Repeated PyTorch L-BFGS and an independent matrix-free Gauss--Newton/LSMR
solver reached `||r-iI||_2 = 1.11046e-4` and operator error `2.82906e-4`.
The Jacobian adjoint check is accurate to `1.2e-16`, but all deep Krylov solves
hit their iteration caps, so stop numerical polishing. Algebraically, with
`A=rho_U(a_2)`, `E=rho_U(c_2)`, and fixed `B=rho(b_1)`, `C=rho(c_1)`, the
equation reduces exactly to `(BABE)^2=iC`. Here `A,E` are commuting
involutions with four 16-dimensional joint eigenspaces. Attack this finite
square-root factorization by spectral projectors and character matching; it
is now higher yield than further continuous descent. Details and solver
records: `experiments/atlas_self_similarity_refine_results.md`.

The multiplicities compress once more: the 64-dimensional restrictions are
eight copies of a canonical 8-dimensional package, namely `2*tau` plus the
four linear `D8` characters versus two copies of every `V4` character. Hence
an exact `U(8)` solution of `(BABE)^2=iC` amplifies to the observed 64D model.
`experiments/atlas_self_similarity_block8_search.py` instantiates this
minimal package; its exact recognition is recorded below.

That block-eight search has succeeded and been made exact. In the canonical
block let `S=(0 7)(1 6)(2 5)(3 4)`,
`P=(0 6)(2 4)(3 5)(1 7)`, `F=(I+iC)/sqrt(2)`, `A=BPB`, and `E=PSF`.
Then `A,E` are commuting self-adjoint involutions, all four joint eigenspaces
have dimension two, and `BABE=SF` with `(SF)^2=iC`. Thus the survivor relation
is exactly `i I_8`, and eightfold amplification gives `i I_64` inside the two
honest `A8` charts. Sage verifies the identities exactly over `Q(zeta_8)` in
`experiments/atlas_self_similarity_block8_exact.py`. The one-relator phase
gate is complete; stop optimizing it. The remaining algebraic gate is whether
this class survives after centralizing *all* Leavitt relators, i.e. in
`R/[P,R]`, followed by the negative-corner construction. Full proof:
`docs/FALSE_SELF_SIMILARITY_PHASE_SEED.md` and
`experiments/atlas_self_similarity_refine_results.md`.

The complete radius-ten audit prevents overinterpreting that theorem. The
eightfold exact alignment makes exactly fourteen of the 234 boundary words
scalar, namely the whole conjugacy/inversion class `C_11`; they are `+/- iI`
to below `5.4e-15`. None of the other 220 words is scalar and none of the 178
perfect-overlap-certified zero words maps to identity. The remaining maximum
centrality defect is `1.7375382832`, with boundary RMS `1.4149416221`. Thus
the model does not factor through `P/[P,R]`. The next finite solver must force
representatives of the 24 certified-zero classes to identity while retaining
the exact `C_11` phase, then use the incompatibility pattern for multiplicity
coupling or a multi-chart filling proof. Full audit:
`experiments/atlas_self_similarity_global_audit.py` and
`experiments/atlas_self_similarity_global_audit_results.md`.

The four persistent worst classes near the exact phase do not themselves
give an algebraic obstruction.  All of indices `70,86,90,91` and phase class
`11` lie in a local `S4*S4`.  After imposing the four zero words, this local
presentation has a quotient of order `168` (the degree-eight `PSL(2,7)`)
where class `11` is a nontrivial involution.  Hence no proof using only those
four relations plus the local `S4` laws can kill the phase.  The finite
certificate cannot extend to the ambient simple `A8` factors, so the next
exact target is to exploit certified-zero words outside the local slice to
force ambient-chart extension.  Full proof and audit:
`docs/FALSE_ATLAS_STUBBORN_S4_QUOTIENT.md` and
`experiments/atlas_stubborn_s4_certificate.py`.

The ambient-extension escape is real, not merely local.  The 178
perfect-overlap-certified zero words reduce to 24 cyclic classes.  Exhausting
all `40,320` automorphisms between the two full `A8` factors finds 14 inner
and 12 outer alignments killing all 24 representatives.  Eight inner and all
12 outer solutions keep class `11` nontrivial; an explicit outer solution
maps it to an involution.  Hence class `11` is not in the normal closure of
the entire currently certified package.  This still does not prove survival
in `R/[P,R]`, because the finite `A8` image of class `11` is not central.
The next finite quotient search must impose phase centrality, or a larger
exact atlas scan must find new zero relators eliminating all 20 witnesses.
Full theorem and exhaustive certificate:
`docs/FALSE_ATLAS_CERTIFIED_A8_QUOTIENT.md` and
`experiments/atlas_certified_a8_alignment.py`.

Centrality does not rescue the local four-class obstruction. The central
quotient of the local `S4*S4` presentation maps onto the perfect group
`PerfectGroup(2688,2) ~= (C2^4):PSL(3,2)`, whose center has order two. Both
local `S4` factors embed, the four zero classes map to one, and class `11`
maps to the central involution. The negative central eigenspace of the
regular representation restricts as `56 lambda_S4`; amplifying 15 times
matches `lambda_A8|S4 = 840 lambda_S4`. Hence two honest regular `A8` charts
in dimension `20160` satisfy all four zeros exactly and send class `11` to
`-I`. Any obstruction must now use at least one of the other 20 certified
classes. Full exact proof and permutation certificate:
`docs/FALSE_ATLAS_LOCAL_CENTRAL_PHASE.md` and
`experiments/atlas_stubborn_s4_certificate.py`.

The simultaneous 24-class solver now gives a first finite compatibility
answer.  With the two `(5,2,1)` `A8` charts fixed, `U(64)` reaches certified
zero-class RMS `1.279437` while retaining the survivor phase to HS error
`0.008520`.  A symmetry-broken full `U(128)` multiplicity-two search reaches
`1.271406` at phase error `0.008401`; its off-block HS mass is `0.334236`, so
the small improvement is genuine rather than a duplicated block.  Zero-only
searches plateau near RMS `0.65` and erase the phase.  Stop broad weight/seed
sweeps in this ansatz.  The preceding finite quotient rules out an exact
obstruction from the four persistent local classes alone.  Add relations
outside their `S4*S4` slice to force ambient-chart extension, or enlarge the
actual vertex irrep multiplicities.  Full scoped result:
`experiments/atlas_self_similarity_multirelator_results.md`.

The exact outer quotient yields a stronger continuous bridge.  The
outer-stable 128-dimensional representation
`rho directSum (rho after theta)` has an alignment which kills all 24
certified classes to `6.5e-15`.  After symmetry breaking, the central target
`-I` gives a new balanced point: zero RMS `0.352252`, zero maximum `0.555910`,
phase HS `0.212666`, phase operator `0.412192`, and phase trace `-0.977386`.
At phase weight ten the phase improves to HS `0.057228` and operator
`0.115708` with zero RMS `0.491114`.  This is decisively better than the `iI`
front.  Multiplicity two does not scale: a symmetry-broken full `U(256)` run
improves the balanced weighted objective by only `0.205%`, with errors still
`(0.352035,0.212209)`.  Stop this fixed outer-pair family and additional
same-dimensional `iI` seeds.  Change the actual vertex irrep content.  Details:
`experiments/atlas_self_similarity_multirelator_results.md`.

Explicitly adding all twelve phase commutators to the exact 30-dimensional
outer-tangent model does not produce a nonlinear central phase.  A
kernel-directed start at weight one ends with all-identity RMS `0.480563`,
maximum `1.368373`, and phase HS `1.366428`; weights `0.1` and `10` remain on
the same two finite-quotient strata.  The exact 136-dimensional tangent kernel
and phase rank 60 are first-order information only.  Stop generic `U(30)`
L-BFGS.  Solve its second-order kernel equations, or couple the exact
order-2688 local central block to the 20 outside classes in induced/regular
coordinates.  Full numerical scope:
`experiments/atlas_self_similarity_multirelator_results.md`.


Free-product conjugacy reduces the 56 apparent survivors further. After
exact cyclic reduction, they form four classes up to conjugacy and inversion,
each of size fourteen, represented by collision-tree indices
11, 30, 44, and 55. All representatives have cyclically reduced length
eight, and none is conjugate to its inverse. Since conjugacy is trivial and
inversion is negation in \(R/[P,R]\), the entire first-boundary package is
generated up to sign by at most these four central classes. Work with these
four representatives, not the eight projection pairs. Reproducible exact
classification and proof are in FALSE_SELF_SIMILARITY_PHASE_SEED.md and
experiments/atlas_survivor_conjugacy.py.

The first genuinely multi-chart filling closure is also exact.  The 178
known perfect-overlap relators collapse to 24 cyclic classes.  Repeatedly
attaching arbitrary cyclic conjugates of those chart cells while keeping the
cyclic boundary length at most eight reaches a fixed point after six cells:
the layer counts are `24,222,462,480,148,22`, for 1,358 classes total, and
none of the four survivor representatives occurs.  Thus every filling which
admits this cyclic attachment ordering must cross intermediate boundary
length at least ten.  At width ten, 13,234 classes occur through three cells;
reverse layers of 292 and 5,200 tagged classes exclude every
cyclic-attachment filling of area at most five.  This is a width barrier, not
nontriviality in `R/[P,R]`; larger
boundaries, nonshellable diagrams, or new chart cells remain live.  Exact
search and proof scope:
`experiments/atlas_survivor_chart_filling.py` and
`docs/FALSE_ATLAS_CHART_FILLING_WIDTH.md`.

The obvious nonorthogonal interpolation between the complementary exact
endpoints is also closed.  For tensor flip `J` and the unique wall alignment
`L_k`, the relative permutation has `(J^*L_k)^4=1`, so there are only eight
square-root branches up to scalar.  A balanced implicit regular-space scan
gave boundary mean projective loss at least `0.9937`, wall-failure mean at
least `0.9676`, and shared-control mean at least `0.8301` for every branch.
Do not run more branches or seeds in this one-operator functional calculus.
Full signal: `experiments/atlas_boundary_geodesic_results.md`.

The natural enlargement of the genuine prefix-swap symmetry is exhausted as
well.  Every two-sided coordinate twist has the form `w_M=M_2 v`; it still
exchanges the two atlas factors exactly when
`M_2 in K_2 intersect N_Q(K_1)`.  Exact enumeration of all 20,160 matrices,
with Leavitt chart membership decided over `F_2`, gives

`K_2 intersect N_Q(K_1)={1}`.

Thus this whole family acts only by the already-known
`11 <-> 55`, `30 <-> 44` swap and cannot identify the final two central
classes or make either self-inverse.  This does not compute the full Leavitt
normalizer or rule out unrelated inner symmetries.  Exact proof and audit:
`docs/FALSE_ATLAS_TWISTED_SWAP_NO_GO.md` and
`experiments/atlas_twisted_swap_normalizer.py`.

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
