# The first-order constant of the two-S3 covariance collapse, exactly

Session record, 2026-08-19.  Instruments:
`experiments/atlas_asc_packet_build.py`,
`experiments/atlas_asc_covariance_gpu.py`,
`experiments/atlas_asc_tangent_ratio.py`,
`experiments/atlas_asc_tangent_exact.py`.
Target: `research/atlas-two-s3-covariance-collapse`, whose open claim (ASC)
is the last missing prerequisite of `nonhyperlinear-from-two-s3-covariance-
collapse`, itself one edge from the goal `non-hyperlinear-group`.

**Status of the claim after this session: still OPEN.**  What is new is a
sharp, exactly rational, first-order half of it, and a machine-checkable
reduction of that half to positivity of one explicit element of `Z[A_8]`.

## 1. What was computed

The canonical regular-`A_8` criterion puts every analytic unknown into one
relative chart unitary `U in U(20160 k)`,

    pi_U(h) = lambda(h) (x) I_k          (h in K_1),
    pi_U(h) = U (lambda(h) (x) I_k) U^*  (h in K_2).

A GPU implementation of that model at `k = 1` (dense `U`, 20160 x 20160)
reproduces the certified classical fold exactly: at `U = I` all **234**
first-boundary words have defect `0.0` and the interior separator
`c_19243 = [p1_12, q_19243]` has defect `1.413007 = sqrt(2)`, matching the
`ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT` statement (17).  That gate is the
correctness anchor for everything below.

Because the fold is an exact zero of the boundary sub-packet, the local
behaviour there is a pair of quadratic forms.  For `U = exp(eps A)`:

    ||pi_U(s) - 1||_2^2 = eps^2 || sum_j lambda(p_j)[A,lambda(g_j)]lambda(q_j) ||_2^2 + O(eps^3),
    a^2 + b^2           = eps^2 ( ||[A,lambda(h_a)]||_2^2 + ||[A,lambda(h_b)]||_2^2 ) + O(eps^3).

## 2. The telescope that makes it exact

Each boundary word has total product `1` in `A_8`, so its suffix is forced:
with `u_j = g_1...g_(j-1)` and `v_j = u_j g_j` one gets `q_j = v_j^(-1)` and

    lambda(u_j) [A, lambda(g_j)] lambda(q_j)
        = lambda(u_j) A lambda(u_j)^(-1) - lambda(v_j) A lambda(v_j)^(-1).

Every first-order term is therefore a **difference of conjugations**.  With
the conjugation representation `rho(x)A = lambda(x) A lambda(x)^(-1)` and

    z_s   = sum_j (u_j - v_j)   in Z[A_8],
    W_pkt = sum_s z_s^* z_s,
    W_cov = sum_(h in {h_a,h_b}) (h-1)^*(h-1) = 4 - 2 h_a - 2 h_b,

the two forms are exactly `<A, rho(W_pkt) A>` and `<A, rho(W_cov) A>`, so
the sharp first-order constant is one generalized eigenvalue problem for a
pair of positive elements of the **integral group algebra**:

    C_loc = max { lambda : rho(W_cov) x = lambda rho(W_pkt) x }.

Group-algebra elements have the same spectrum in any module containing every
irreducible constituent, and both the conjugation module and the left regular
module do, so the computation is done on the 20160 x 20160 group matrices in
double precision.  No probes, no optimizer, no manifold: 69 seconds on one
A100, of which 33 s is enumerating `GL(4,2)`.

## 3. Results

| tangent packet | words | dim ker W_pkt | cov energy on that kernel | constant |
|---|---|---|---|---|
| certified-24 representatives | 24 | 2358 | **6.000000000009** | first-order **escape** |
| tangent-5 = words 0, 11, 30, 44, 55 | 5 | 120 | 2.18e-17 | `C = 1.000000000000068` |
| all first-boundary words | 234 | 120 | 2.36e-17 | `C = 0.07142857142857525 = 1/14` |

Three things follow.

**(a) The kernel is the `H`-fixed space, and 234 words do not shrink it.**
`120 = [A_8 : H] = 20160/168` is exactly the dimension of the permutation
module on `A_8/H`, i.e. of the `H`-fixed space summed over all irreducibles
with multiplicity.  The node records the kernel statement for five words as
an exact rational certificate; this says the entire first-boundary packet
has the **same** derivative kernel, so no further boundary word adds any
first-order information.  That is a sharpening in the direction the node
cares about, and it is also a warning: the boundary packet is first-order
saturated at five words.

**(b) Local coercivity holds, with rational constants.**  On the kernel the
covariance energy is `1e-17`, so at first order every direction that keeps
all 234 boundary words also kills both raw `S_3` covariances, and

    a^2 + b^2 <= (1/14) * sum_(s in 234 boundary words) ||pi_U(s)-1||_2^2 + O(eps^3),
    a^2 + b^2 <= 1 * sum_(s in {0,11,30,44,55}) ||pi_U(s)-1||_2^2 + O(eps^3).

Against the proved floor `a^2+b^2 >= 1/40` of
`raw-swap-forces-two-s3-covariance-energy`, the first inequality says a
hypothetical microstate near the fold must carry total boundary energy at
least `14/40 = 0.35`, hence `max_s ||pi_U(s)-1||_2 >= sqrt(0.35/234) = 0.0387`.

**(c) The 24 certified representatives are genuinely weaker.**  Their kernel
is 2358-dimensional and carries covariance energy exactly `6`, so there is a
first-order direction killing all 24 while moving both covariances.  Any
proof that quotes the certified-24 alignment set alone cannot reach (ASC),
even infinitesimally.  The five tangent words are doing the work.

## 4. What this does not settle

It is a statement at the classical fold only.  The exact characteristic-two
countermodel recorded in the node -- `E = M semidirect A_8`, `dim_F2 M = 155`,
all 234 boundary words vanishing exactly with the two `H` copies disagreeing
-- is a global object, and no local constant touches it.  The node's item 5
("boundary plus one interior separator") remains the target: what is now
available is the *local coercivity half* of it, with an explicit constant,
which is the input item 5 says the tangent gap should supply.

One thing that IS uniform: the constant does not depend on `k`.  At
multiplicity `k` the same two elements of `Z[A_8]` act by
`rho_k(x)A = (lambda(x) (x) I_k) A (lambda(x) (x) I_k)^(-1)`, the conjugation
module `M_(20160k)` still contains every irreducible constituent, and the
generalized spectrum of a pair of group-algebra elements depends only on
which irreducibles occur.  So `C_loc = 1/14` at every multiplicity, which is
exactly the dimension-freeness `(ASCq)` demands -- at first order.  What
remains missing is global, not dimensional.

## 4b. It was never a first-order statement

Re-deriving the telescope without the `eps` gives an exact product formula.
Put `f(g) = [U, lambda(g)] = U lambda(g) U^(-1) lambda(g)^(-1)` and
`V_x = rho(x)U`.  For a fold-trivial word each telescope factor is
`V_(u_j) V_(v_j)^(-1)`, and fold-triviality is exactly what makes the
factors compose, so for EVERY unitary `U` and every one of the 234 words

    pi_U(s) = prod_j rho(u_j)( f(g_j) ),        (exact, no remainder)

with `a = ||f(h_a)-1||_2` and `b = ||f(h_b)-1||_2`.  The atlas criterion is
therefore a holonomy system in conjugated commutators, on the group rather
than on a tangent space.

Consequently both energies are quadratic forms in `U` itself:

    a^2+b^2 = <U, rho(W_cov) U>,     sum_s l_s^2 = <U, rho(W_pkt) U>,
        l_s = ||rho(z_s) U||_2,

so the generalized eigenvalue bound

    a^2 + b^2 <= (1/14) sum_s l_s^2

holds for EVERY matrix `U` at EVERY multiplicity -- it is global, not a
Taylor statement.  What is first order is only the identification of `l_s`
with the true defect `||pi_U(s)-1||_2`.  The whole remaining gap in the local
half of (ASC) is therefore the single inequality

    sum_s l_s^2 <= C' * sum_s ||pi_U(s)-1||_2^2.                    (LINK)

`pi_U(s) - 1 = sum_j (W_j - 1) + cross terms`, and in normalized HS the cross
terms are NOT second order: `||(A-1)(B-1)||_2` only gives
`||A-1||_op ||B-1||_2`.  That is precisely the operator-norm-versus-HS gap
that separates MF from hyperlinear, so (LINK) cannot come from a Taylor
estimate, and it is where the difficulty of this route now sits.

## 4c. No inner far branch exists

`experiments/atlas_asc_inner_link_scan.py` decides the inner case exactly, in
integer arithmetic: at `U = lambda(t)` the true defect of a word is `0` or
`sqrt(2)`, and `l_s^2` is the sum of squared integer coefficients of
`sum_j (lambda(u_j t u_j^(-1)) - lambda(v_j t v_j^(-1)))`.

Scanning all 20160 inner chart conjugators: **exactly one** kills all 234
first-boundary words, namely the identity, and there `l_s = 0` for every
word.  So (LINK) has no inner counterexample, and the far components that the
characteristic-two countermodel exhibits are necessarily non-inner.  The
repository previously had this uniqueness for the five-word tangent screen;
this is the full packet.

## 4d. The same element, in two characteristics

`z_s = sum_j (u_j - v_j)` is the integral lift of the characteristic-two
derivative of the rank-three audit: that audit's

    d_q = sum_(j in chart 2) (p_(j-1) + p_j)   in F_2[A_8]

is the same formula, with `p_(j-1) = u_j` and `p_j = v_j`, reduced mod 2.  So
the two objects the lane has been computing with are one object in two
characteristics:

  * over `F_2`, the left ideal `I = sum_q F_2[A_8] d_q` has codimension 155,
    and `M = F_2[A_8]/I` is what carries the affine countermodel;
  * over `C`, the positive element `W_pkt = sum_s z_s^* z_s` has kernel of
    dimension 120 = [A_8 : GL_3(2)] and gives the constant 1/14.

The countermodel lives in the mod-2 cokernel; the coercivity lives in the
complex kernel.  Anyone attacking (LINK+) inherits both descriptions of the
same 234 signed prefix sums, which is the practical reason to expect the
interior separator -- which is what closes the mod-2 hole -- to be exactly
what the complex inequality is missing.

## 4e. The countermodel, evaluated exactly

The characteristic-two countermodel is not just a qualitative obstruction --
every energy in it is computable in closed form, because its second chart is
INNER in `E`.  With `M = F_2[A_8]/I`, `m = 1+I` and
`beta(g) = ((1+g)m, g)`, the second chart is conjugation of the first by
`mu = (m, e)`, so the intertwiner is the group element `U = lambda_E(mu)` and

    rho(x)U = lambda_E(x . m),
    <U, rho(x)U> = delta( (1+x)m = 0 ),

since normalized traces in a regular representation are `delta_(h,e)` and the
trace is conjugation invariant.  Both energies collapse to one membership
test in the left ideal `I`:

    sum_s l_s^2 = sum_(x in Z) (W_pkt)_x,   Z = { x : 1+x in I },
    a^2+b^2     = 4 - 2[h_a in Z] - 2[h_b in Z].

Measured (`experiments/atlas_asc_countermodel_energy.py`, 73 s):

| quantity | value |
|---|---|
| left ideal rank / queue remaining | 20005 / 0 (reproduces the audit) |
| raw `S_3` letters fixing `m` | neither |
| covariance energy `a^2+b^2` | **4**, the maximum |
| `sum_s l_s^2` | **1372** = 2^2 * 7^3 |
| support of `W_pkt` inside `Z` | 3 of 101 |
| boundary defect | 0 |
| interior defect squared | 2 |

Two consequences.

**The global 1/14 bound survives a test it could have failed.**  `4 <= 1372/14
= 98`.  The bound came from a complex generalized eigenvalue problem on
20160 x 20160 matrices; this value came from GF(2) ideal membership in a
model at multiplicity `2^155`.  Nothing forced them to agree.

**The constant of (LINK+) is at least 686.**  The countermodel has zero
boundary defect and interior defect squared 2, so any valid `C'` satisfies
`C' >= 1372/2 = 686`.  That does not threaten the route -- it needs only some
finite dimension-free constant, and against the `1/40` floor even `C' = 686`
leaves `sum_(S_0) defect^2 >= 1/(40 * 49)` -- but it is a hard calibration,
and it says the interior separator has to do a lot of work.

**A dichotomy for group microstates.**  For any microstate whose chart
unitary is a group element `mu` in an overgroup, `<U, rho(x)U> = delta(x in
Z)` with `Z = Stab(mu)`, so `sum_s l_s^2 = sum_(x in Z)(W_pkt)_x =: E(Z)` and
`rho(x)U = U` exactly when `x in Z`.  Since `ker rho(W_pkt)` is the `H`-fixed
space, `E(Z) = 0` iff `H <= Z` iff both raw letters fix `mu` iff the
covariance vanishes.  For this whole class of models the collapse is
therefore equivalent to a subgroup containment, with no analysis in it at
all.

## 5. The proof-shaped residue

`C_loc <= C` is equivalent to positivity, in every representation of `A_8`,
of the single element

    C * W_pkt - W_cov   in Z[A_8]        (support 101 and 3 group elements).

That is a finite rational statement about one element of an integral group
algebra of order 20160: checkable in exact arithmetic irrep by irrep (14
irreducibles, dimensions up to 70), or by exhibiting a sum-of-squares
certificate `C W_pkt - W_cov = sum_i y_i^* y_i` in `Q[A_8]`.  Either form is
small enough to be certified rather than measured, and is the natural next
artifact for this lane -- and, unlike the tracial SOS route the node rules
out in its item 6, this positivity is inside a *finite* group algebra, so
the ruled-out obstruction does not apply to it.

## 6. Reproduction

    python3 experiments/atlas_asc_packet_build.py --out experiments/atlas-asc-packet.npz
    python3 experiments/atlas_asc_tangent_exact.py --words all
    python3 experiments/atlas_asc_tangent_exact.py --words tangent5
    python3 experiments/atlas_asc_tangent_exact.py --words certified24
    # and the U = I gate of the full model:
    python3 experiments/atlas_asc_covariance_gpu.py --init identity --iterations 0

Raw outputs: `experiments/asc-exact.json`,
`experiments/asc-exact-tangent5.json`, `experiments/asc-exact-certified24.json`,
`experiments/asc-bench.out`.  Evidence, not proof: the eigenvalues are
double precision, and Section 5 is what would make them a certificate.
