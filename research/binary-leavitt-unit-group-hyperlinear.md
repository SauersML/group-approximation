---
rg: 2
id: binary-leavitt-unit-group-hyperlinear
kind: claim
title: The binary Leavitt unit group, the first nonsofic group, is hyperlinear
distinct_from:
  leavitt-steinberg-hs-unstable: that is a normalized-HS *stability* statement about the Steinberg cover St_5(L), which yields a hyperlinear nonsofic *central quotient* only through the stability fork; this asks directly whether the nonsofic group itself has Hilbert--Schmidt models, with no stability hypothesis and no cover
  openai-leavitt-unit-nonsofic: that is the established nonsoficity theorem for this group; this is the orthogonal approximation question about the same group, and the two are compatible -- their conjunction is exactly the Q3.4 separation
  hyperlinear-nonsofic-group: that asks for *some* hyperlinear nonsofic group; this pins the candidate to one now-explicit group, so it can be attacked with that group's structure rather than searched for
artifacts:
  - research/artifacts/leavitt-semisimple-path-algebra-marked-projective-gap-2026-09-08.md
  - research/artifacts/wreath-three-cycle-projective-trace-gap-2026-09-08.md
  - research/artifacts/leavitt-unit-root-marked-subgroup-projective-gap-2026-09-08.md
  - research/artifacts/leavitt-unit-product-marked-subgroup-projective-gap-2026-09-08.md
  - research/artifacts/leavitt-native-heat-entanglement-breaking-distance-2026-09-08.md
  - research/artifacts/leavitt-root-receiver-double-centralizer-and-compression-calibration-2026-09-08.md
  - research/artifacts/leavitt-all-finite-coefficient-projective-gap-2026-09-08.md
  - research/artifacts/leavitt-finite-coefficient-rank-gap-2026-09-08.md
  - research/artifacts/leavitt-two-finite-factor-expectations-and-robust-intersection-2026-09-08.md
  - research/artifacts/leavitt-relative-cut-recursion-accumulation-2026-09-08.md
  - research/artifacts/leavitt-coordinate-expectation-lift-exclusions-2026-09-08.md
  - research/artifacts/leavitt-poissonization-and-admissible-time-rounding-equivalence-2026-09-08.md
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
  - research/artifacts/leavitt-center-normalizer-rounding-criterion-2026-09-08.md
  - research/artifacts/leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md
  - research/artifacts/leavitt-regular-trace-cp-reversal-2026-09-08.md
  - research/artifacts/leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md
  - research/artifacts/leavitt-compressor-lamp-displacement-ledger-2026-09-08.md
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
  - research/artifacts/leavitt-internal-kazhdan-gap-and-external-commutant-2026-09-08.md
  - research/artifacts/leavitt-single-c-trace-certificate-2026-09-08.md
  - research/artifacts/leavitt-full-character-classification-2026-09-08.md
  - research/artifacts/leavitt-packet-perfect-kernel-and-finite-amalgam-obstruction-2026-09-08.md
  - research/artifacts/leavitt-eight-word-reduction-and-s3-repair-2026-09-08.md
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

OPEN.  Does `L_{F_2}(1,2)^x` -- or its finitely generated nonsofic subgroup
`G = EL_D(R)` from `openai-leavitt-unit-nonsofic` -- admit normalized
Hilbert--Schmidt models?  Equivalently, is `L(G)` Connes embeddable?

**Manuscript consequence, checked 2026-09-08.** A positive answer would
give a hyperlinear nonsofic group and a canonical hyperlinear non-MF
trace. It would not make the canonical trace on `C*_(max)(H)` amenable:
`binary-leavitt-unit-group-fails-factorization-property` proves that
trace is nonamenable, using property `(T)` and failure of residual
finiteness. Thus it is not itself Brown's amenable nonquasidiagonal
witness. The current manuscript `non_mf_groups_exist.tex`, Section
`sec:amenable-nonqd`, obtains that witness independently from its
Clifford group `W`. The hyperlinearity question for this same `H`
remains the objective on either branch.

**Current analytic frontier, 2026-09-08.** Uniform Kazhdan heat rounding
alone is now a sufficient unproved premise for nonhyperlinearity of H.
The new artifact specifies its quantifiers and proves the reduction.
A rounded global heat allows small generator corrections into the
rounded algebra's commutant, followed by component selection preserving
all relations and canonical traces. Slower heat times and a scaled SOS
error budget make the selected model's full global commutant scalar.
A second use of rounding, after restriction to the isomorphic native
subgroup L, produces a nonzero trace-zero element of that same global
commutant's center, a contradiction. The proof requires no independent
factorial-embedding or center-control hypothesis. The universal rounding
premise remains unproved, and no hyperlinearity verdict is claimed.

The conditional implication has passed a further independent audit,
including its full-commutant identification and native generation
identity. The time quantifier can be weakened: rounding at some
admissible time for each canonical model implies rounding at every
admissible time for that model, with the same algebras. This follows
from the integrated SOS energy bound. On the other hand, general
heat structure does not simplify the unrestricted channel problem.
For any near-idempotent self-adjoint bistochastic UCP map P, its
Poissonization `Q_t=exp(-t(I-P))` satisfies
`||Q_t-P||_(infinity->2)<=2 exp(-t)+(t-1+exp(-t)) delta`,
where `delta=||P^2-P||_(infinity->2)`. At logarithmic time the
difference tends to zero, and the generator has residual
`(I-P)^2-(I-P)=P^2-P`. Thus unrestricted rounding remains equally
hard even with this abstract heat and gap structure. The fixed
adjoint words and actual group-algebra certificate remain additional
features of H's problem.

The sufficient premise now has an exact published commutant
formulation. [Alekseev--Thom Open Problem 6.2(a)](https://arxiv.org/html/2608.05362v1#S6)
asks for finite-algebra representatives of Kazhdan-group relative
commutants, allowing dimension ratios tending to one. For canonical
H embeddings, equality of the induced expectations upgrades to
uniform heat approximation by a coordinate-witness argument; the
proved corner theorem removes the negligible dimension change.
Thus a positive answer to 6.2(a) for every canonical embedding of H
would imply H nonhyperlinear by the two-use theorem. Conversely,
H hyperlinear would force a negative instance of 6.2(a) for H itself.
This is conditional on either missing input, not a decision of H's
hyperlinearity. Part (b), which asks for exact centralizers of
corrected generator lifts, is not needed.

Two abstract commutant constructions do not supply rounding
counterexamples. The expectation onto the commutant of the initial
tensor copy of the hyperfinite II_1 factor in a matrix ultraproduct
has no uniformly bounded coordinate retraction at all, by a
moving-Pauli diagonal argument.
An outer-involution expectation likewise has no coordinate
bistochastic UCP lift: full-matrix tracial stability makes its
coordinate reflection inner. Native SOS heat does provide a
coordinate expectation; its finite-algebra rounding remains the
separate unsolved step.

Native heat also cannot be replaced by a measure-and-prepare channel:
its infimum distance in `infinity->2` to bistochastic
entanglement-breaking channels tends exactly to one. A finite Weyl
test proves the bound `k tau(p)/(k+1)` for such a channel's error
when fixing a copy of M_k in a corner p. The native commutant
contains the canonical II_1 factor of the commuting fourth-coordinate
copy K, hence every fixed M_k; its matrix units lift to corners of
trace tending to one. Letting k grow after taking the microstate
limit proves the lower bound, and scalar expectation gives the upper
bound one. This excludes that classical intermediate step; rounding
onto general noncommutative matrix algebras remains unproved.

The rounding-boundary artifact now proves linear rounding for every
Schur UCP channel: `||P_C-E_B||_(infinity->2)<=18||P_C^2-P_C||_(infinity->2)`.
This excludes the entire Schur class as a source of counterexamples,
but does not cover the noncommuting native generators. Little
Grothendieck also gives a dimension-independent `sqrt(2)` bound for
all normalized tracial amplifications of an `infinity->2` map, plus
physical-corner localization of its middle spectral space. Neither
statement supplies positivity of the spectral cutoff. A separate
proved lemma rounds a compression of an exact finite-algebra
expectation with error at most `25 alpha^(1/4)`, where `alpha` is the
discarded dimension fraction; thus the specified flexible-dimension
rounding formulation suffices as well. The June 2026 tracial Ulam
stability theorem repairs maps from an existing exact matrix algebra.
Extracting that source algebra from a native heat map remains unproved.

Two further classes now admit actual extraction. Channels diagonal
in an orthonormal projective group unitary basis, including Weyl/Pauli
channels, round with error at most `2 delta` for `delta<1/10`.
Self-adjoint bistochastic channels of any one fixed Kraus rank also
round uniformly in matrix dimension: their finite Kraus frame becomes
an exact finite-dimensional source algebra in the ultraproduct, whose
matrix units lift through almost full corners. This second theorem
does not apply automatically to heat with finitely many generators.
For canonical models of any infinite group and times tending to
infinity, heat purity `chi_n^2=Tr_super(P_n^2)/d_n^2` tends to zero,
and every bistochastic channel of Kraus rank at most `r` remains at
distance at least `1/sqrt(r)-chi_n`. Thus an asymptotically exact
fixed-rank reduction is unavailable for H's heat maps. A modulus
usable with growing rank remains missing.

A stronger frame norm does not supply that modulus. Exact canonical
finite-quotient models of `SL_3(Z)` have zero SOS residual and heat
converging in `2->2` norm to their exact commutant expectations, while
the trace-norm distance between the Kraus frames of P and P-squared
tends to the maximum value two along slow heat times. Positive
random-walk speed and a common Gram orthogonalization prove this
separation. The same slow-diagonal comparison applies conditionally
to canonical H-models. Thus canonicality and fixed Kazhdan SOS cannot
upgrade channel near-idempotence to small frame trace-norm defect.

There is also a rank-independent sufficient compact-group criterion:
if a compact matrix group is uniformly eta-fixed by P, and the bounded
image of P has distance theta from its generated algebra A, then
`||P-E_A||_(infinity->2)<=theta+3 sqrt(eta^2+epsilon)`.
The image admits an explicit four-almost-fixed-unitary decomposition,
but taking the group generated by those unitaries is invalid: a
two-dimensional exact-gap heat example has almost-fixed generators
whose long products have fixing defect tending to one. Selecting a
group satisfying the required whole-group bound remains unproved.

Generic metric approximate closure cannot select that group in the
same dimension: compressed irreducible representations of
`PGL_2(F_q)` give scalar-saturated compact sets with multiplication
defect tending to zero but distance at least `1/100` from every
compact subgroup. One extra dimension removes this obstruction.
Moreover, any bistochastic CP channel uniformly fixing these specific
sets approaches the identity, so the example does not refute CP
rounding. Both qualifications are proved in the boundary artifact.

The two finite generating factors give a proved robust-intersection
theorem under approximate commutation of their averaging expectations:
`EFE` has Kraus rank at most `3*8*3=72` and idempotence defect at
most `||EF-FE||_(infinity->2)`, so the bounded-rank theorem extracts
an algebra in that case. But the original pair in every canonical
H model satisfies `liminf ||EF-FE||_(infinity->2)>=sqrt(7)/12`.
The exact identity `AB intersect BA=A union B`, followed by the
canonical Kraus-frame calculation, proves this bound. Thus that
positive theorem cannot be applied directly to the native pair.

A recursive low-energy-cut attempt also needs a global budget.
For exact tensor diagonal expectations, slightly rotating each
successive binary cut gives arbitrarily small local relative costs
while the final algebra stays at distance tending to one from the
correct expectation. The same happens with strictly positive
vanishing channel defects. A global bound on the energy divided by
the trace of every terminal projection stops this example; the
existence of an informative partition satisfying that bound is not
proved.

The finite-algebra estimates supporting this reduction include a
dimension-independent reversal theorem for conjugate finite-dimensional
algebras: reverse inclusion error is at most `sqrt(2R)` times forward
error, where `R=max(t_j/a_j^2)/min(t_j/a_j^2)` measures trace weights
against simple block degrees. Matrix factors and canonical finite-group
algebras, including their commutants, have `R=1`. Applying this theorem
to the native heat maps proves that any conditional-expectation
approximation with error `eta=O(sqrt(epsilon log(1/epsilon)))` must have
`R=Omega(1/(epsilon log(1/epsilon)))`. Existence of an approximation with
controlled `R` would therefore contradict canonical microstates of H;
that additional approximation theorem remains unproved. The strengthened
central-corner estimate shows that every retained corner with distortion
at most `R_0` must omit trace mass at least `1/(2(R_0+1))`; an isolated
vanishing-trace outlier cannot supply the necessary distortion.

A stronger reversal bound now controls central complexity directly:
`reverse^2<=2k forward^2` for `k` simple central blocks, independently
of all degrees and weights. It follows that any such heat rounding
also requires `k=Omega(1/(epsilon log(1/epsilon)))` at the stated error
scale. The countable-flow extension excludes a purely atomic limiting
center: uniform expectation rounding would force a nonzero diffuse
part in `Z(pi(L)' intersect product_omega M_n)`. This remains a useful
necessary condition on a rounded native model; the newer selection
argument avoids assuming a purely atomic center separately.

The same overlap-flow estimates now construct a bounded nonconstant
central function, not just a diffuse-part obstruction. Under uniform
rounding there are self-adjoint `z_n in Z(A_n)` with trace zero,
`||z_n||_op<=1`, `||z_n||_2>=1/8`, and
`||[U_n,z_n]||_2=O(delta_heat,n+eta_n) -> 0`. They also
asymptotically commute with `L` and its complementary copy `K`.
The full Leavitt complement gives the stronger native identity
`H=<L,uKu^(-1)>`, and an explicit fixed word controls the coordinate
swap as well. Thus these heights actually lie in the center of the
full external H-commutant. For one arbitrary embedding that need not
be a contradiction. The new two-use rounding argument first selects
a model with scalar global commutant and then rules out its L-heat
rounding, making the universal rounding premise sufficient by itself.

There is also a sufficient route without any bound on trace weights:
round the native heat expectation to a finite algebra whose center all
native generator matrices normalize, allowing `o(1)` generator corrections.
Their atom permutations would give a sofic image of H and must therefore
be trivial by simplicity and nonsoficity. Fiberwise matrix-factor reversal
then contradicts the native reverse heat defect. The simultaneous
center-normalizer rounding required by this criterion is not proved.

The criterion cannot be justified solely by asserting that all native
corner centers commute. The center-normalizer artifact now constructs
an exact finite-factor extension of the canonical `H` representation
with scalar whole-`H` commutant, but anticommuting central unitaries in
the relative commutants of two conjugate native rank-three corners.
This rules out that structural inference even with ambient factoriality.
No embeddability is asserted for the extension, so a matrix-specific
theorem or a suitable embedding selection remains possible.

The established `24k`
relative-unitary criterion characterizes this question by vanishing of
every finite kernel-stage infimum. The explicit Thompson test packet now
has eight words: an exact commutator identity removes one of the original
nine, and a conjugacy replaces another by `d^2`. Its maximum defect
satisfies `E_8<=E_9<=2 E_8` in every dimension. The new artifact also
proves an explicit normalized-HS repair of the derived `S_3` pair while
keeping its order-three matrix fixed. That repair has not been lifted
through the prescribed Leavitt generator words. No uniform packet gap
or full-kernel microstate construction has been proved.

The `24k` criterion also has an equivalent scalar-relator formulation.
If `Delta_m^sc` minimizes distance of each listed relator to the scalar
unitaries, then `Delta_m^sc<=Delta_m<=sqrt(2) Delta_m^sc`.
Tensoring a tuple with its entrywise conjugate removes all phases at
once, preserves regularity of both frozen finite factors, and restores
the same chart in dimension `24K`, `K=24k^2`. No compatibility of the
chosen phases across relators is needed. This relaxes the explicit
positive target; no tuples attaining vanishing scalar defect have
been constructed. Relators merely close to a nonscalar center do not
satisfy this criterion.

The marked finite-coefficient obstruction now covers every semisimple
coefficient-generated algebra A_0, without an ambient representation.
For any projective representation of the marked subgroup with
trace-zero c,
`49 L(r_*)+24 L(R_v)+24 L(R_0)>=beta`, where
`beta=sqrt(2-2sqrt(2/5))`. Thus some defect is at least `beta/97`.
Balanced path-algebra components use internal coefficient extraction;
the unequal-rank components form three-cycle factors handled by an
exact character estimate. The shared cycle remains in a semidirect
product throughout. This includes coefficients that generate a full
finite matrix algebra, even with singular ts and no invertible root
coefficient. Semisimplicity is required of the algebra generated by
the tuple; it cannot be inferred from the ambient matrix algebra.

There is also an explicit scalar-HS gap for three genuine kernel words
over every nonzero finite unital characteristic-two coefficient ring A,
including rings with a nilpotent radical. If the complex representation
extends projectively to all of `EL_3(A)`, then, writing
`L(g)=dist_2(rho(g),T I)`,
`L(c)<=144 L(r_*)+24 L(R_v)+24 L(R_0)`.
Thus `tr(rho(c))=0` forces a relator defect at least `sqrt(2)/192`,
independently of both dimensions and representation multiplicities.
Preusser's eight-conjugate extraction and an exact five-term
coefficient identity replace the earlier unspecified finite-simple-group
covering constant. The same argument covers semilocal
characteristic-two rings. Representations of the marked subgroup need
not extend to the full elementary group, and the needed auxiliary
conjugators need not belong to that subgroup. Arbitrary `24k` unitary
tuples have no established coefficient-ring realization. The
unrestricted criterion is still open.

One restricted marked-subgroup case does avoid the extension
assumption. If the coefficient ring is directly finite and satisfies
the literal equality `ts=1`, then `st=1` and the marked subgroup
generated by `c,x_12(s),x_12(t),x_12(v)` is exactly `EL_3(A_0)`,
where A_0 is the unital coefficient subring they generate.
An elementary diagonal conjugation sends `R_0=x_12(tvs)` to
`x_12(v)`, giving `L(c)<=6 L(R_v)+12 L(R_0)` and gap
`sqrt(2)/18`. This assumes an exact equality in the coefficient
ring; small or zero projective defect of r_* does not supply it.

The extension assumption can now also be removed when `ts` is any
unit in a finite coefficient ring. Conjugating by
`diag(1,Z^-1,Z)`, with `Z=ts`, exposes constant roots and an internal
finite coefficient ring B. The transformed marked group contains
`EL_3(B)` normally, with cyclic quotient of order at most three.
A three-block representation handles the induced coefficient
automorphism, and an internal nine-term coefficient identity gives
`L(c)<=49 L(r_*)+24 L(R_v)+24 L(R_0)`, hence gap `sqrt(2)/97`.
All conjugators are inside the marked subgroup. Unit orders divisible
by three and nilpotent radicals are allowed. An explicit F_64 example
has original coefficient ring F_64 but transformed group
`SL_3(F_8) x C_3`, so identifying the marked group with the full
original coefficient group would be false.

The same bound now holds under the broader condition that
`x_13(z)` belongs to the marked group for some unit coefficient z.
This does not require `ts` to be a unit. For example, it applies if
v is a unit, or if any sum of coefficient words of lengths `2 mod 3`
is a unit. It even covers `s=e_12,t=e_21,v=0` in `M_2(F_2)`:
all three coefficients and `ts=e_22` are singular, but `st+ts=1`
supplies the needed root. The proof uses three automorphic images
of each defect coefficient and bounds every root in the recovered
ring, including the conjugate defining j. Assignments without such
a unit root remain outside this argument. Arbitrary frozen unitary
tuples still have no established coefficient-ring realization.

The existence of this unit root has an exact finite-algebra test.
Form the path algebra P generated by the three coordinate idempotents
and the nine cyclic forward root increments. A unit backward root
exists precisely when those three idempotents have equal ranks in
every simple factor of `P/J(P)`. Fixed factors under c automatically
satisfy this; failures occur in orbits of three with unequal ranks.
Such failures really occur, even when s,t,v generate `M_4(F_2)`:
`s=e_13+e_42,t=e_23+e_41,v=e_34` have a graded coefficient module
of dimensions `(2,1,1)` that makes every candidate coefficient
singular. That example still has a separate gap: whenever `v^2=0`,
the exact identity `R_v=d` gives `L(c)<=L(r_*)+2L(R_v)`.
Thus failure of the normalization criterion does not imply failure
of a projective obstruction.

The semisimple theorem closes those unequal-rank cases when the path
algebra has zero radical. The identities
`<P,c>=M_3(A_0)` and `J(P)=P intersect M_3(J(A_0))`, together
with averaging over the order-three cycle, prove that P is
semisimple exactly when A_0 is. For the trace step,
`(M x N^3) semidirect C_3` and an involution j_b in N^3 satisfy
`1-|tau(c)|^2<=(5/3)(1-|tau((j_b c)^2)|^2)` in every projective
representation. Localized extraction bounds the balanced part of j
using the full relators, leaving this exact three-cycle situation.
The remaining finite-coefficient cases can have a nonzero radical
and unequal coordinate ranks; quotienting out that radical is not
justified in an arbitrary complex representation. The passage from
arbitrary H microstates to finite coefficient models remains unproved.

Full feasible tuples also cannot be jointly monomial in one common
basis, even with arbitrary scalar phases or vanishing generator
perturbations. Their permutation projection would give a sofic image
of H; simplicity and nonsoficity kill that image, after which
perfectness kills the remaining diagonal image. Tensor-conjugation
gives the same exclusion for scalar-relator sequences. This does not
exclude individual finite packets or general unitary tuples.

The new finite trace certificate gives an explicit relation list and
error bound promoting `tr(c)=0` to canonical traces on any prescribed
finite set. Thus full-kernel feasible tuples themselves become
canonical microstates; no subsequent tensor amplification is needed.
This proves trace recovery, not existence of the tuples.

**The full character classification is now proved in writing.** The
claim `binary-leavitt-full-character-simplex` establishes
`Char(H)={a*1+(1-a)*delta_1:0<=a<=1}` on the entire group, extending
the earlier core-only theorem. Thus an actual nonembeddable character
of this same `H` would settle the negative branch. That construction
remains open. The proof also identifies exactly which subgroup
characters extend; a bad character of a hyperlinear subgroup cannot.

The eight-word quotient has a split finite quotient `C_2^3` and a
perfect kernel generated by eight conjugate embedded Thompson groups.
Their separate hyperlinearity does not give a compatible joint model.
The new packet-structure artifact excludes the natural finite-field
amalgam over `S_3` as a source of the third commuting involution; it
does not exclude arbitrary unitary or approximate extensions.

## Why this question cannot have an uninteresting answer

Since 2026-08-01 there are unconditional nonsofic groups.  For any such `G`,
exactly one of the following holds, and each closes a root of this graph --
one of them the program goal:

```text
G hyperlinear      =>  hyperlinear nonsofic group      =>  q3-4-resolved (No)
G not hyperlinear  =>  the first nonhyperlinear group  =>  non-hyperlinear-group
```

Before 2026-08-01 no group was known to sit on either side of that fork, so
no single group could be a fork machine.  That is the structural change the
new nonsoficity theorems make, and it is why a decisive analytic verdict on
*one* explicit nonsofic group is now worth more than the same verdict on an
arbitrary candidate.  The same disjunction applies verbatim to
`kun-thom-nonsofic-wreath` and to Fournier-Facio's torsion-free examples
(arXiv:2608.02025); this node pins the first and best-understood one.

Note the asymmetry with the stability lane.  `leavitt-steinberg-hs-stability-fork`
is also a dichotomy over the same algebra, but it is mediated by normalized-HS
stability of the *cover* `St_5(L)` and reaches hyperlinearity only through a
central quotient.  The present question skips both mediations.

## Attempts

**Transfer the coefficient rank obstruction to complex representations.**
For `Z=ts`, set `f=1+Z^3`, `q=v^2+Z`, and `p=tvsZ^2`.
In each simple matrix quotient, `3 rank(f)+rank(q)+rank(p)>=d`.
Consequently one is a sum of five terms `alpha z beta`, with z of
types f,f,f,q,p. Lifting through the Jacobson radical and absorbing
one unit inverse preserves that exact five-term count. Preusser's
Proposition 9(i) extracts each f term using eight conjugates of r_*;
double commutators extract q and p terms using four conjugates each.
The six-root expression for c proves the explicit constant 192 over
every finite, and more generally semilocal, coefficient ring of
characteristic two. The earlier projective-support and normal-generation
proof remains a separate proof for semisimple finite coefficient rings.
These two full-ring proofs need ambient representations. The subsequent
unit-root theorem instead recovers an internal coefficient ring and
handles the remaining order-three quotient. The semisimple theorem
also covers unequal coordinate ranks through an exact three-cycle
character bound. Neither needs ambient extension in its stated class.
Nonzero radicals with unequal coordinate ranks remain outside that
combined reduction. No coefficient realization is supplied for
arbitrary H tuples.

**Recover a coefficient root from group centralizers.** This specific
shortcut fails in the native group. With `a=x_12(1)`,
`b_1=x_12(s_0)`, and `v=s_0 t_1+s_1 t_0`, the literal word
`K_0=(b_3 j)^3=diag(v,v,1)` centralizes a, but
`[K_0,b_1]=x_12(v s_0 v+s_0)` is nonidentity: its coefficient
satisfies `t_1(v s_0 v+s_0)v=1`. Thus the full root is not in
the double centralizer of a. There is nonetheless an explicit native
g with `g x_12(r) g^-1=x_12(s_0 r t_0)` for every r. The subgroup
generated by this entire additive root and g is locally finite by
infinite cyclic and has explicit canonical permutation models.
The global one-root compression itself therefore supplies no
approximation obstruction; further relations between root positions
are necessary.

**Check what the heat assumption adds.** Poissonization converts
every uniformly near-idempotent self-adjoint bistochastic UCP map
into a nearby heat map with an approximate gap-one residual identity.
Consequently a proof using only those analytic features would already
prove the unrestricted rounding theorem. For native heat, integrated
SOS retention separately shows that only one admissible time per
canonical model needs to be rounded. Neither argument constructs
the finite algebra required by (R).

**Exclude a trace-frame shortcut and simplify the positive matrix target.**
For positive-speed group heat, the probability laws at times t and 2t
become asymptotically disjoint. In sufficiently slow canonical matrix
models, their two Kraus frames retain this trace-norm separation.
The exact `SL_3(Z)` benchmark simultaneously has genuine heat rounding,
so small frame trace defect is not necessary for the desired conclusion.
Independently, the native relative-unitary optimization can measure
distance to scalar relators: tensor-conjugation removes phases with
only the explicit `sqrt(2)` loss and retains the frozen separator.

**Extract the Kraus algebra when its rank is bounded.** Haar averaging
identifies mean-square channel defect with Hilbert--Schmidt defect of
the positive Kraus frame. At fixed rank, the limiting frame identities
make the Kraus span a finite-dimensional unital star algebra. Its
coefficient identities survive every representation, so lifting its
matrix units produces exact expectation channels uniformly close to
the original ones. Canonical long-time heat fails the needed fixed
rank reduction: fixed-time Poisson expansions and heat monotonicity
give vanishing purity, hence the explicit `1/sqrt(r)-o(1)` distance
from all rank-r bistochastic channels. The frame argument cannot
simply discard rank dependence; `(E_diagonal+E_scalar)/2` has frame
Hilbert--Schmidt defect tending to zero but channel defect exactly
`1/4` and distance at least `1/12` from every expectation.

**Separate compact-group selection from its repair.** Functional
calculus and the Kraus commutator energy express each bounded image
element as a four-unitary linear combination up to
`epsilon^(1/3)`, with fixing errors of the same order. Once a compact
group with uniform fixing and image approximation has been selected,
Haar projection of an adjoint-paired Kraus family into its commutant,
followed by one defect-filling Kraus operator, gives the rank-free
rounding estimate above. The explicit Pauli `M_2` heat example shows
that forming the generated group does not supply such a selection.

**Test and narrow the uniform rounding premise.** The exact assignment
formula for Schur multipliers turns a large entrywise idempotence
defect into a large matching. Deleting its small endpoint set leaves
near-zero or near-one Gram coefficients; Gram transitivity gives a
partition algebra. Comparing retained errors directly with the
original defect gives the linear constant 18. This argument works
also for complex correlation matrices. Separately, little
Grothendieck controls normalized matrix amplification and localizes
bad spectral directions to a small physical corner. An exact
expectation can develop a middle eigenvalue under such compression,
but its compression can itself be rounded by trimming product-form
blocks and rotating them into the desired corner, with the explicit
`25 alpha^(1/4)` bound. The remaining task is construction of the
initial algebra; repairing an already parametrized UCP map from one
is handled by Stinespring dilation and Haar averaging.

**Use uniform heat rounding twice.** The new selection theorem starts
with a single rounded global heat for an ICC property-(T) group.
Haar averaging and polar completion correct its generators into the
rounded algebra's exact commutant, without repairing group relations.
Componentwise heat errors average in squared norm; ICC conjugacy
averaging makes the component trace squares tend to zero. A component
can therefore retain scalar heat rounding and canonical microstates.
Penalizing its SOS defects by the heat time preserves identification
of the full external commutant, which becomes scalar. For H, universal
rounding supplies a second instance on the isomorphic subgroup L;
the native height then contradicts that scalarity. Only the rounding
premise remains unproved in this conditional route.

**Extract a central function and close the native generation step.**
The central-overlap flow has negligible upward cost and a positive
downward cost. A median and a clipped function of `log(t_i/a_i^2)`
give an actual self-adjoint central height of variance at least `1/64`
whose compressor commutator is at most
`sqrt(2/(1-exp(-1/16)))` times the forward expectation defect.
Heat rounding supplies the `L` commutators, and centrality supplies
the complementary `K` commutators. For the second Leavitt pair a,b,
the identities `ba=1`, `ea=a`, `be=b` show that `uKu^(-1)` contains
`x_14(ar)` and `x_41(rb)`. Commutators with roots of L supply all
remaining roots, proving `H=<L,uKu^(-1)>`. Thus the height lies in
`Z(pi(H)' intersect M)`. The fixed swap spelling also gives a finite
quantitative ledger. The newer component-selection argument handles
this global center under the universal rounding premise.

**Use central overlap flow instead of trace distortion.** For conjugate
finite algebras, physical overlaps of central supports form a balanced
flow. Haar covariance bounds both directional losses along each edge.
Decomposing into cycles gives `reverse^2<=2k forward^2`; passing to a
countable balanced flow proves reversal whenever the sorted central
physical weights are tight. An ultraproduct of finite algebras has
purely atomic center exactly under that tightness condition. Since the
native reverse heat defect tends to one, uniform expectation rounding
would force a nonzero diffuse central part. This proves a stronger
necessary condition on hypothetical models; it does not exclude the
remaining diffuse case or establish the rounding theorem.

**Use nonsoficity on one exposed finite center.** The center-normalizer
artifact proves `reverse^2<=2 forward^2+mu`, where `mu` is the physical
trace of center atoms moved by the compressor. If all native generators
normalize that center, weighted atom permutations define a sofic image
of H, so `mu -> 0`. Together with uniform expectation rounding this
would prove nonhyperlinearity without global trace-weight control. The
native identities have not supplied the common normalized center; even
approximate normalization of a fixed center need not allow a small exact
normalizer correction when atom ranks differ.
More decisively, the new class-two lamp extension preserves every
native group identity and canonical trace in a finite factor with
scalar whole-group commutant, while two conjugate native corner
centers contain anticommuting unitaries. Ordinary tracial structure
therefore does not imply the needed common center. The extension is
not asserted Connes embeddable and does not disprove a special matrix
rounding theorem for H.

**Reverse heat inclusion after controlling the trace weights.** The new
regular-trace reversal artifact proves the needed matrix inequality for
exact finite algebras by Haar averaging and a covariance calculation.
The native heat-rounding artifact supplies the actual unitary witness and
the quantitative obstruction
`chi_t <= 3eta+sqrt(2R)(delta_t+3eta)`, with `delta_t -> 0` and
`chi_t -> 1/sqrt(2)`. Under full canonical microstates the reverse
heat defect in fact tends to its maximal possible value, `1`, on the
native compressed unitary. Thus bounded trace distortion is sufficient; a
trivial center is not required. The remaining input is uniform
`infinity->2` approximation of the native heat maps by conditional
expectations with suitably controlled `R`. Spectral rounding provides
an orthogonal projection but does not establish complete positivity
or an algebraic range. The new rounding-boundary artifact also shows
that canonical factorial trace and property `(T)` can coexist with a
macroscopic center in the external commutant. That example still has
bounded distortion and does not refute the weaker sufficient input.
The fixed SOS certificate does identify the ultraproduct heat map with
the full external relative-commutant expectation: an integrated energy
bound retains every bounded asymptotically commuting sequence. This
identification is not a lift of the range to finite matrix subalgebras.
The rounding-boundary artifact now proves uniform approximate
multiplicative closure of the heat image, while a three-state matrix
heat example shows that neither spectral cutoff nor taking powers
automatically produces the needed expectation.
It also now gives a concrete distinction from ordinary HS stability:
rank-one compressions of irreducible projective-plane representations
of `SL_3(Z)` yield canonical property-(T) microstates with every fixed
SOS residual controlled and uniform scalar heat rounding, yet they
stay uniformly far from exact representations in their dimensions.
Thus representation repair would demand more than heat-algebra rounding;
this example does not supply the latter for H.

**Quantify native displacement before reversing inclusion.** The native
compressor produces a bilateral chain of independent commuting involutions.
At depth `m`, a half-coset supplies `M=2^(m-1)` unitary vectors commuting
with `L`, whose compressed commutator displacements are exactly orthogonal
with norm `sqrt(2)` in canonical trace. The new lamp ledger promotes this
to a finite-word trace estimate and a direct spectral-projection leakage
bound of order `M/(n^2(1+M*xi^2))` in matrix dimension `n`, when the fixed
separation and commutator-error parameters are controlled. This is an
actual-H construction. It requires dimension-dependent depth and trace
accuracy to yield positive ambient density; fixed-stage microstate
feasibility supplies no such coupling.

**Use positive heat maps to avoid unbounded spectral projections.** A
fixed Kazhdan SOS certificate and the native compressor rows give heat
inclusion and approximate idempotence with operator-unit-ball error
`O(sqrt(epsilon*log(1/epsilon)))`, independent of dimension. But the new
heat artifact constructs unitarily conjugate finite conditional
expectations with exact gap one and equal spectra for which one-sided
inclusion error tends to zero while reverse inclusion fails on a unitary
by a norm tending to one. The example also has commuting complementary
algebras and satisfies the analytic energy comparison with fixed
constants. It refutes this CP/spectral inference; it does not satisfy
the full native H presentation. Additional H-specific input is needed.

**Upgrade compression to the 2-norm using both native Kazhdan copies.**
For `L=EL_3(R)` on the first three coordinates and `K=R^x` on the
fourth, the new internal-gap artifact proves `C_H(L)=K`, `C_H(K)=L`,
and `L(L)' intersect L(H)^omega=L(K)^omega`, with an explicit
Kazhdan Poincare inequality. These are internal assertions in the
exact group factor. The H-specific tracial extension
`H *_L (L times Z)` preserves all native identities but has a larger
L-commutant even though the ambient H-commutant is scalar. Thus the
desired control in external matrix approximants requires additional
matrix-approximation input. The artifact makes no embeddability claim
for that extension, and even an external commutant identification
would leave the required finite-dimensional concentration control.
The same artifact proves that both the compressed inclusion and the
inclusion of the two commuting native factors have infinite Jones index.
Consequently finite-index rigidity is not directly applicable.

**Read it off the nonsoficity proof.**  Dead as stated: the nonsoficity proof
runs through one-sided compression `t Gamma t^{-1} <= Gamma` plus property (T)
plus a commuting non-LEF subgroup, and every step that kills permutation
models is a *refinement* argument that the trace cannot see.  This is the
whole content of `trace-blindness-sharpness` and of the `II_1` branch
surviving `invariant-size-collapse`: the compression mechanism is exactly the
one to which the normalized trace is blind.  So the mechanism that supplies
nonsoficity gives no signal in either direction here.

**Use the coefficient algebra's failure of direct finiteness.** This
does not decide it. The Leavitt algebra is not directly finite, but
`leavitt-unit-group-algebra-not-directly-finite` and
`leavitt-group-algebra-not-stably-finite` remain open claims about its
modular group algebra. The quotient onto the Leavitt algebra does not
prove either claim. Moreover no implication from hyperlinearity to
positive-characteristic direct finiteness is supplied here. Over `C`,
group-algebra direct finiteness follows from the canonical finite trace
independently of hyperlinearity.

**Build a model from the Leavitt structure.** The
natural source is the tower of finite-rank corners; the obstacle is that the
defining Leavitt relations `t_i s_j = delta_{ij}`, `s_0 t_0 + s_1 t_1 = 1`
are exactly the relations of a non-stably-finite algebra, so an approximate
matrix model must break one of them by a `2`-norm-small amount while keeping
the group relations of `EL_D(R)` exact enough.  That is the same tension
`corner-renormalization-cost` measures.

**Negative branch.** The open uniform-gap claim and the now isolated
bad-character claim both concern this exact group. Neither the finite
packet reductions nor the character classification proves that branch.

**Transport the compression criterion to normalized 2-norm.** Dead as
stated (2026-09-09): `hs-analogue-of-normal-kazhdan-criterion-is-false`.
The sofic models of the manuscript's group `W` are 2-norm asymptotic
representations satisfying every group hypothesis of the criterion
(Kazhdan core, central order-two witness in the defect) and keep the
witness at 2-norm distance `sqrt 2`.  So compression plus a normal
Kazhdan subgroup of the defect obstructs nothing in normalized
Hilbert--Schmidt norm, and a 2-norm obstruction for `H` must use
information the criterion does not: conjugation by the compressor is
not 2-norm controlled (`||Ad(diag(-1,1,..,1)) - 1|| = 2` while the
matrix is 2-norm close to `1`).  Independently, Kirchberg's theorem
(`binary-leavitt-unit-group-fails-factorization-property`) means a
positive answer would not make the canonical trace of `H` amenable.
