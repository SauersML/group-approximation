# Wave 2: quantitative centrality at the GHB7 expanding-block frontier

2026-09-20. Written mathematics, not Lean-certified. The hyperbolic
residual-finiteness problem, GHB7 stability, and expanding-block rounding
remain open. This note extends the wave-1 scalar-relator calculation;
it does not overwrite that proof.

## Result

There are two rigorous conclusions.

1. On a fixed-scalar-gap doubled GHB7 tuple, small relator defects can
   be rephased so that their size is bounded linearly by their failure
   to commute with the generators. Constants depend on the scalar gap
   and fixed, finite presentation certificates, not matrix dimension.
   This is a quantitative extension of exact-central rounding, but
   corrects scalar phases only and does not remove noncentral defects.
2. Even arbitrarily strong relative approximate centrality with respect
   to the **raw** defect does not simplify the unresolved stability
   problem. Scalar phases can enlarge the raw power-relator defects
   while preserving both the scalar gap and all centrality errors.
   Any hypothetical instability witness can therefore be made to
   satisfy centrality_error=o(raw_defect^k), for any fixed k>0.

The quantitative comparison identifies the normalization needed in a
further argument: centrality must be measured against defect after
removing generator scalar phases. With that normalization, the two
quantities are already comparable; no iteration gain follows.

## 1. Definitions and retained input

Write W=(A^+,A^-,B^+,B^-,C^+,C^-) and use the standard eleven GHB7
relators r_1,...,r_11 on U=(A^+,B^+,C^+). Three are a^7,b^7,c^7 and
eight are iterated commutators. Let

    delta(W)=max_l ||r_l(U)-I||_2,
    kappa(W)=max_{l,t} ||r_l(U)W_t-W_t r_l(U)||_2,

where t ranges over all six entries. Norms are normalized HS norms.
Operator commutators in the energy are additive. Group commutators
inside presentation words and the Hopf certificates are multiplicative.
The copy-equality defect, separately, is

    e_copy(W)=max_{s in {a,b,c}} ||W_s^+-W_s^-||_2.

Assume a fixed scalar conjugation gap c>0:

    (1/24) sum_t ||[W_t,X]||_2^2
       >= c ||X-tr(X)I||_2^2                       (SG)

for all matrices X. The gap is for the entire doubled tuple. No gap
for the plus entries alone is assumed.

The wave-1 theorem `hrf-ghb7-scalar-relator-models-round-strictly`
proves that H_2(GHB7;Z) is killed by m=2401. For the free presentation
F/N, Hopf's formula identifies H_2 with
(N intersect [F,F])/[F,N]. Consequently each of the eight commutator
relators r_i has

    r_i^m in [F,N].                                (1)

Fix once and for all, for each i, a finite expression of r_i^m as a
product of commutators [f,n], or their inverses, with f in F and n in N.
For every such n, fix a finite expression as a product of conjugates
of the eleven defining relators and their inverses. Let L_i be the
total number of these relator occurrences, summed over the chosen
commutators in the expression for r_i^m. Set

    K=max_i(m+2L_i),
    a_c=1/sqrt(2c),
    B_c=a_c(1+pi K/(2m)),
    delta_*=min(1/4, sin(pi/(2m))).                  (2)

These are finite constants. This proof does not claim a numerically
optimized or computed value of K. The existence of finite certificates
in (1) is proved by the wave-1 multiplier calculation; one can find
certificates by enumerating finite free-word identities until all eight
are found. Thus K is a fixed presentation constant, not a new analytic
hypothesis, but this note supplies no running-time estimate for finding it.

## 2. Phase elimination with a dimension-free bound

**Theorem.** If (SG) holds and delta(W)<delta_*, there are phases
alpha_a,alpha_b,alpha_c in T such that, writing

    W'_s^sign=alpha_s W_s^sign,

the following hold:

    delta(W') <= B_c kappa(W),
    max_s |alpha_s-1| <= (pi/7)delta(W),
    kappa(W')=kappa(W),
    e_copy(W')=e_copy(W),
    scalar_gap(W')=scalar_gap(W).                  (3)

In particular no HS-to-gap transfer is used: scalar rephasing preserves
all conjugation operators exactly.

**Step 1: expansion supplies nearby scalar phases.** For R_l=r_l(U),
(SG) gives

    ||R_l-tr(R_l)I||_2 <= kappa/(2sqrt(c)).

Since ||R_l-I||_2<1/4, tr(R_l) is nonzero. Define
lambda_l=tr(R_l)/|tr(R_l)|. A unitary R satisfies

    ||R-lambda I||_2^2=2(1-|tr(R)|)
       <=2(1-|tr(R)|^2)=2||R-tr(R)I||_2^2.

Therefore

    ||R_l-lambda_l I||_2 <= a_c kappa.              (4)

Also |lambda_l-1|<=2|tr(R_l)-1|<=2delta.

**Step 2: evaluate the fixed Hopf certificates.** A product of L
conjugates of defining relators and their inverses is within
L a_c kappa of the scalar obtained by replacing each relator by its
lambda phase. This is ordinary telescoping of products of unitaries;
conjugating words contribute no extra factor because scalars commute.

If n is within L a_c kappa of a scalar unitary, then for every unitary
F the multiplicative commutator [F,n] is within 2L a_c kappa of I.
Apply this to the fixed expression (1) to obtain

    ||R_i^m-I||_2 <=2L_i a_c kappa.

Separately, (4) and telescoping give
||R_i^m-lambda_i^m I||_2<=m a_c kappa. Hence

    |lambda_i^m-1| <= (m+2L_i)a_c kappa <=K a_c kappa. (5)

This step does not assume the original relators are exactly scalar or
that their values define a character of N/[F,N]. It evaluates a fixed
exact identity in the free group and estimates each occurrence.

**Step 3: select the root near 1.** Write lambda_i=exp(i theta_i) with
theta_i in [-pi,pi]. Since |lambda_i-1|<=2delta and
delta<sin(pi/(2m)), one has |theta_i|<pi/m. On this interval,

    |lambda_i-1| <= |theta_i|
       <= (pi/(2m))|lambda_i^m-1|.

Combining this with (4)-(5) gives, for every commutator relator,

    ||R_i-I||_2 <=B_c kappa.                        (6)

**Step 4: remove the three scalar power phases.** For s=a,b,c choose
the seventh root alpha_s of lambda_(s^7)^-1 whose argument is nearest
zero. Then

    |alpha_s-1| <=(pi/14)|lambda_(s^7)-1|
                <=(pi/7)delta.

The rephased power relator is lambda_(s^7)^-1 U_s^7, whose defect is
at most a_c kappa by (4). Every iterated commutator is unchanged by
generator scalar phases, so (6) controls its defect. This proves the
first two assertions of (3). The last three follow exactly: powers
are multiplied by scalars, commutators are unchanged, both copies of
each generator receive the same scalar, and Ad(alpha_s W_s)=Ad(W_s).

## 3. What the estimate does and does not round

Define the defect after optimal scalar rephasing by

    delta_phase(W)=min_{alpha in T^3} delta(alpha W).

The minimum exists by compactness. For every alpha, centrality is
unchanged, and commutating with a unitary gives

    kappa(W)=kappa(alpha W)<=2delta(alpha W).

The theorem therefore proves

    kappa(W)/2 <=delta_phase(W)<=B_c kappa(W)        (7)

whenever the original tuple has delta<delta_* and gap c. The upper
bound is attained up to its stated constant by phases tending to 1,
not by arbitrary distant character twists.

This does not give a contraction iteration: phase correction leaves
kappa exactly unchanged. A second application cannot improve the
right-hand side of (3). Removing the nonscalar residual requires a
different operation with a proved estimate.

There is a genuine, but restricted, exactness criterion. If additionally
(A^+)^7=(B^+)^7=(C^+)^7=I, the original defect is entirely on the eight
commutator relators; (6) then gives

    delta(W)<=B_c kappa(W).                         (8)

Consequently an exact-order-seven tuple with delta<delta_* and
kappa<=theta delta for some theta<1/B_c must have delta=0. Its plus
entries already form a genuine representation in the original
dimension. If copy defects tend to zero, that representation rounds
both copies. No assertion here says the exact-order-seven condition
can be imposed on arbitrary expanding tuples without losing the gap.

## 4. Scalar phase camouflage defeats raw relative-centrality tests

**Theorem.** Fix any k>0. Suppose W_n is a fixed-gap doubled GHB7
asymptotic representation which stays a positive distance from every
flexible rounding. There are scalar rephasings W'_n, tending to W_n
in operator norm, which have the same scalar gap and satisfy

    kappa(W'_n)=o(delta(W'_n)^k),                    (9)

while still having no flexible rounding. The copy-equality defects
are unchanged and tend to zero. This theorem is conditional on the
existence of an instability witness; none is asserted to exist.

**Proof.** Put epsilon_n=max(delta(W_n),e_copy(W_n)). If epsilon_n=0,
the tuple is already genuine, so an instability witness has epsilon_n>0
eventually. Pass to a tail and set t_n=epsilon_n^(1/(k+1)). Multiply
both a entries by exp(i t_n), leaving b,c unchanged.

All eight commutator relators and all copy-equality defects are
unchanged. The a-power relator is multiplied by exp(7i t_n); all
other power relators are unchanged. Hence

    |exp(7i t_n)-1|-epsilon_n <=delta(W'_n)
        <=|exp(7i t_n)-1|+epsilon_n,

so delta(W'_n)/(7t_n)->1. Centrality is exactly invariant under
these phases and kappa(W_n)<=2delta(W_n)<=2epsilon_n. Thus

    kappa(W'_n)/delta(W'_n)^k
       <=O(epsilon_n/t_n^k)=O(epsilon_n^(1/(k+1)))->0.

The scalar conjugation gap is exactly invariant. The generator change
is at most |exp(i t_n)-1| in operator norm. Flexible rounding cost is
1-Lipschitz in the maximum generator 2-distance, by applying the same
candidate genuine representation and compression to both tuples.
Thus a positive rounding-cost lower bound persists on a tail.

The same argument with t_n tending to zero more slowly can enforce
any prescribed finite list of power-law relative-centrality bounds.
It follows that, for any fixed k>0, proving flexible rounding for
every fixed-gap sequence satisfying (9) would already prove the full
open GHB7 expanding-block criterion. It is not an independently easier
special case. In contrast, delta_phase is unchanged under this
camouflage, and (7) correctly detects the remaining noncentral error.

## 5. Why the spectral-sector extension stops

The wave-1 exact-central theorem used simultaneous eigensectors of
relator matrices that reduce every generator. On each such sector,
the evaluated relators defined an actual scalar-projective model,
so the 2401-root conclusion was exact.

For approximate centrality, a spectral cut of a relator need not
reduce the generators. Pinching and polar correction may make the
generators block diagonal, but the relators of those changed generators
need not equal the original scalar values on each cut. Word telescoping
only controls the new errors; it does not make them scalar or central.
Thus the exact-central argument cannot be applied a second time
without proving a new correction statement.

The estimate above is precisely what survives without that missing
step: finite multiplier certificates force scalar phases near 1 and
leave an error proportional to centrality. It does not authenticate
the approximately invariant spectral cuts as exact projective sectors.
The phase-camouflage theorem additionally shows why a favorable ratio
against the unnormalized defect cannot fill this gap.

## 6. Review and next technical boundary

The wave-2 stability auditor independently checked Sections 1-5 and
returned PASS on 2026-09-20. The review checked the 1/24 energy
normalization, radial trace estimate, root-selection interval, fixed
Hopf-certificate error count, exact preservation of all conjugation
operators under rephasing, and the phase-camouflage scale and rounding
cost. This is written review, not formal certification.

One subsequent approach considered preserving finite order while
pruning microscopic sectors after Liu's decomposition. Nearest-root
functional calculus imposes seventh powers but can destroy the scalar
gap on a small subspace. Cutting off small-energy projections can
control discarded rank using the original expanding tuple; however,
unitarizing and imposing finite order on the remaining compressions
can create further small nongapped sectors. No closed estimate for
this iteration was obtained. In particular the doubled-polar trick for
arbitrary contractions does not by itself ensure seventh-order output
unitaries. This is an unproved next direction, not a new premise or
established reduction in the graph.

## 7. Independent review of the cyclotomic-cover construction

Read Sections 1-5 of
`research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md` and the
claim/route `wave2-audit-ghb7-cyclotomic-kazhdan-cover` /
`wave2-audit-cyclotomic-kazhdan-cover-proof`. Verdict on 2026-09-20:
**PASS**, using the explicitly named CCKW structure, central-extension
property-(T), and Kazhdan-cover rounding inputs.

The checks were:

- The index-seven orbit complex has one vertex and edge of each type
  and seven faces with the same oriented boundary. The deck action on
  its rational second homology is the augmentation representation.
  Rational equivariant homology identifies this deck-equivariantly
  with group homology, so the dual is the irreducible six-dimensional
  rational cyclotomic representation.
- The coset cocycle identity gives the monomial embedding into
  K^7 semidirect C_7 with the stated index convention. Restriction to
  K has coordinates a^-i k a^i, hence the seven extension classes are
  the conjugates of the chosen class.
- The inverse-image group contains the full Z^7 kernel, and its
  central diagonal is primitive. Quotienting it gives an exact
  extension by the torsion-free rank-six lattice A=Z^7/diag(Z).
- The seven rational evaluation functionals span the dual of H_2(K;Q)
  and have sum zero. Their map has image the augmentation subspace,
  whose projection to Q^7/diag(Q) is an isomorphism. Integral lattices
  may differ by finite index, which causes no problem: the integral
  transgression has finite cokernel. The five-term sequence gives
  finite abelianization of the preimage L. The stated central-cover
  theorem makes L Kazhdan, and index-seven permanence makes E Kazhdan.
- The proof A^T=0 is integral: (T-I)v=k(1,...,1) forces k=0 by summing
  coordinates, and then v is diagonal. The seventh power of any lift
  of a,b,c lies in A and is fixed by the lift; it is therefore trivial.
  The quotient element ensures that its order is exactly seven.
- Given the still-open finite-visibility premise, the primitive central
  eigenspace representation exists in each finite quotient's regular
  representation. Tensoring one coordinate with the conjugate of its
  neighbor kills the diagonal kernel. Induction gives precisely the
  seven A-characters lambda^(v_j-v_(j+1)); each is nontrivial for m>1.
  Thus there are no A-fixed vectors, while each fixed element of A
  converges to I in operator norm. The named Kazhdan-cover criterion
  applies and excludes flexible rounding. The generator lifts have
  exact seventh powers, while relators are mutually commuting block
  scalars on blocks permuted by the generators.
- In the alternative where all finite central-image orders are bounded,
  their least common multiple M kills every such image. For p coprime
  to M, the nontrivial central C_p in B_c/<z^p> is invisible to every
  finite quotient. Its finite-kernel map onto the hyperbolic group K
  makes that quotient hyperbolic. No bound M is proved to exist.

The construction correctly claims neither that the rank-six cover is
hyperbolic (it contains Z^6), nor that its needed finite quotients exist.
Its conditional noncentral block-scalar models are fully consistent
with the wave-1 exact-central rounding theorem: the generators permute
the blocks, so block scalarity does not imply centrality.
