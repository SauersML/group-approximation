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
