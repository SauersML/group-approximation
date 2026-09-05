# Maximal canonical residuals have quotient-uniform spectral exclusion

Assuming flexible normalized-HS stability of SL_5(Z) fails, one can
extract a canonical approximate sequence with no positive asymptotic
low-energy mass in any finite quotient host. This exclusion survives
every vanishing normalized-HS perturbation, including the corrections
provided by QRC. The conclusion is about spectral mass, not a uniform
positive gap above zero.

## Statement and cutoff quantifiers

Fix a finite symmetric Kazhdan generating set S of G=SL_5(Z), with
h=|S| and constant kappa. If flexible HS stability fails, there is a
canonical inverse-compatible approximate sequence W_j in U(n_j) such
that, writing

    N_j(t)=rank 1_[0,t^2](Delta_(Q_(2n_j),W_j)),

one has

    lim_(t downarrow 0) limsup_j N_j(t)/n_j=0.          (RE1)

Here Q_D is the universal finite quotient for representations of
dimension at most D. Equivalently, for every positive sequence t_j->0,

    N_j(t_j)/n_j -> 0.                                (RE2)

For 2h t^2/kappa^2<=1/2, the universal-host theorem gives the exact
identity

    N_j(t)=sup_(Q finite quotient of G)
      rank 1_[0,t^2](Delta_(Q,W_j)).                   (RE3)

Thus (RE1)--(RE2) are uniform over all finite quotient choices, including
ones depending arbitrarily on j and t. Moreover every inverse-compatible
tuple sequence Z_j with

    max_s ||Z_(j,s)-W_(j,s)||_(2,n_j) -> 0

satisfies the same conclusions. In particular this applies to any QRC
correction of W_j whose generator change tends to zero.

## Constructing a maximal recoverable corner

The existing residual-finite ucp regularization and constant-one
maximally-entangled untensoring arguments imply that canonical flexible
stability would imply full flexible stability. Their contrapositive
therefore supplies a canonical bad sequence U_j in U(d_j), separated
by some eta>0 from corrections having both relative padding and
generator error below eta. See
`positive-canonical-corners-bootstrap-stability-2026-09-05.md`, Section 6.

Call p in (0,1] recoverable if, along an infinite subsequence, there
are projections P_j with rank(P_j)/d_j->p, asymptotically commuting
with all generators, whose unitary polar compressions are flexibly
exactly correctable. Include 0 by convention. All approximation and
correction errors here tend to zero, and the padding is o(rank P_j).
Let alpha be the supremum of the recoverable fractions.

If alpha>0, it is attained on a subsequence: choose recoverable p_l
tending to alpha, then take one sufficiently late index from the lth
witness sequence, larger than all previously selected indices, so that
the rank fraction differs from p_l by at most 1/l and every commutator,
compression, correction, and relative padding error is at most 1/l.
This diagonal is a witness for alpha. Its source indices need not lie
in nested witness subsequences. If alpha=0 use P_j=0.

One has alpha<1. Otherwise the corrected corner and the trivial
representation on its negligible complement give a full flexible
correction on a bad subsequence: replacing a unitary block of relative
dimension 1-p costs at most 2 sqrt(1-p) in normalized HS norm.

Pass to the diagonal subsequence just chosen, put n_j=d_j-rank P_j,
and let W_j be inverse-compatible unitary polar compressions of U_j
to (I-P_j)C^(d_j). Their relative dimension tends to 1-alpha>0, so
they are approximate representations. They are canonical as well:
in any tracial ultraproduct the original canonical tuple generates
N=L(G), an ICC factor. The class of P_j commutes with N, and the
trace-preserving conditional expectation satisfies E_N(P)=alpha I.
Consequently the complementary normalized trace on every nonidentity
group element is zero. Polar compression changes fixed words by o(1).
Applying this observation to every ultrafilter gives ordinary sequential
convergence of the corner traces.

The resulting W_j has no recoverable corner of positive limiting
fraction along any subsequence. Indeed, such a corner with relative
fraction q>0 lifts to the original complementary subspace and remains
asymptotically reducing there. Combining its correction with the old
corner correction gives recoverable fraction

    alpha+(1-alpha)q>alpha,

a contradiction. Orthogonal correction errors and padding add with
their dimension weights. Approximate reduction controls the discarded
off-diagonal blocks. These facts require only a fixed pair of corners,
so no infinite iteration or uniform recovery rate is being assumed.

## Low spectral mass would contradict maximality

Suppose (RE2) fails. Along a subsequence there are t_j->0 and c>0 with
r_j=N_j(t_j)>=c n_j. Put a_j=2h t_j^2/kappa^2 and
xi_j=sqrt(h)t_j+2 sqrt(a_j/(1-a_j)). MSC14 gives

    r_j/n_j<=1/(1-a_j),   xi_j->0.

If r_j<=n_j on an infinite subsequence, its deterministic coisometry
constructs projections R_j of rank r_j and exact representations on
their ranges, with

    ||[R_j,W_(j,s)]||_HS <= sqrt(2) xi_j sqrt(r_j),
    ||W_(j,s)R_j-exact_corner_(j,s)||_HS
      <=xi_j sqrt(r_j).

Pass further so r_j/n_j converges to a positive number. These are
positive recoverable corners, contrary to maximality. The exact corner
is also o(1)-close to the unitary polar compression, by the usual polar
compression estimate. If instead r_j>n_j on an infinite subsequence,
the padded polar version gives a full flexible exact correction of W_j:
relative padding is at most a_j/(1-a_j), and normalized generator
error is at most xi_j. This is a recoverable fraction of one, equally
impossible. Thus (RE2) holds.

For completeness, (RE1) and (RE2) are equivalent by monotonicity of
N_j(t). If (RE1) failed, choose t_l downarrow 0 and increasing indices
j_l with N_(j_l)(t_l)/n_(j_l) bounded below; define a sequence of cutoffs
t_j->0 agreeing with t_l at these indices. This contradicts (RE2).
Conversely, eventual t_j<=t bounds the limsup in (RE2) by the limsup
at any fixed t, which tends to zero under (RE1). Neither statement
asserts that the limsup is zero for every fixed t>0.

Equation (RE3), including exact equality rather than a quotient-index
estimate, is the blockwise host-universality theorem in
`universal-host-captures-all-low-energy-types-2026-09-05.md`.

## Stability of the exclusion under QRC changes

Apply (HU4)--(HU5) from that artifact to W_j and Z_j. If Z_j had
positive normalized count along some vanishing cutoffs epsilon_j,
then choosing t_j->0 slower than both epsilon_j and
max_s ||Z_(j,s)-W_(j,s)||_(2,n_j) would give positive normalized count
for W_j. This contradicts (RE2). Interchanging the tuples proves the
claimed invariance. The proof uses an exact representation extracted
from the spectral space and a positive contraction frame; it incurs no
factor depending on the quotient order.

Therefore extracting all available positive correctable mass leaves a
canonical residual whose exclusion is already uniform over every finite
host and is preserved by QRC's vanishing changes. A contradiction still
requires a new theorem producing positive low-energy mass on such a
residual, or excluding it by another argument. No positive-count theorem
or nonhyperlinear-group endpoint is proved here.
