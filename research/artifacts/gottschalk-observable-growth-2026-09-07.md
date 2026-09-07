# Observable growth for an encoder with a local decoder

Date: 2026-09-07. This is a proof of a conditional surjunctivity criterion
and an obstruction to a proposed universal hypothesis. It is **not a proof
of Gottschalk's conjecture**. The argument below is a mathematical proof;
the companion Python replay checks specified finite algebraic instances.
No Lean verification or priority claim is made.

## 1. Statement, spaces, and conventions

Let `G` be any discrete group, let `A` be a nonempty finite alphabet of
size `q`, and let `tau,sigma:A^G -> A^G` be cellular automata satisfying

    sigma o tau = id.

For `q=1` every map is the identity, so suppose `q>=2`. Write `O` for the
rational vector space of local functions on `A^G`, and put `P=O/(Q 1)`.
Choose a basis `1,psi_1,...,psi_(q-1)` for the rational functions on `A`.
The products of nonconstant basis elements at distinct sites, with finite
nonempty support, give a basis of `P`. Call these colored pattern monomials.

The configuration action is `(g.x)(h)=x(g^(-1)h)`. The induced action on
observables translates their sites. Pullbacks are `Q[G]`-linear, fix
constants, and therefore induce maps on `P`:

    T[f]=[f o tau],       S[f]=[f o sigma],       TS=I.

Let `P_0` be the span of all translates of the one-site `psi_i`. Define
`P_(n+1)` by adjoining to `P_n` the entire translation orbit of every
monomial occurring in `T m` or `S m`, for orbit representatives `m` of
the basis of `P_n`. Each `P_n` is a span of finitely many whole basis
orbits, `P_n subset P_(n+1)`, and `T P_n + S P_n subset P_(n+1)`.

Also define the smaller, unsaturated module

    V_n = sum_{w in {T,S}*, length(w)<=n} w(P_0) subset P_n.

Completion throughout means that pattern monomials are orthonormal.
This specifies a Hilbert space norm; it does not assume that either
automaton preserves a Bernoulli measure. Every finite orbit module `P_n`
completes to a finite Hilbert `G`-module `H_n`. Let

    d_n = dim_G closure_{H_n}(V_n).

Inclusions of the `H_n` are isometric, so adding unused basis orbits does
not change this dimension. The dimension is group von Neumann dimension,
not the ordinary dimension of an infinite-dimensional Hilbert space.

**Theorem.** Put `E=I-ST` and `theta=E|P_0:P_0 -> P_2`, and let

    delta = dim_G closure(theta(H_0)).

Here and below a map between finite orbit modules denotes its bounded
extension when applied to their Hilbert completions. Then:

1. `delta=0` if and only if `tau sigma=id`, equivalently `tau` is surjective.
2. For every `n>=1`, the closed span of
   `theta(P_0),S theta(P_0),...,S^(n-1) theta(P_0)` has dimension exactly
   `n delta`, and

       d_(n+1) >= n delta.

3. If `liminf_(n->infinity) d_n/n = 0`, then `tau` is bijective.
   It is enough that the larger weighted orbit count

       b_n = sum_{orbits m in P_n} 1/|Stab_G(m)|

   has `liminf b_n/n=0`, since `d_n<=b_n`.

Every injective finite-alphabet full-shift automaton has such a local
decoder. Thus these conclusions apply to any injective `tau` and each
choice of its local decoder. The constant `delta` depends on the actual
pair; no universal positive lower bound or integrality is asserted.

## 2. Finite orbit modules and the analytic facts used

If a nonconstant pattern has finite nonempty support `F` and stabilizer
`H`, choose `f in F`. The map `h -> hf` injects `H` into `F`, so `H` is
finite. Its orbit module is `Q[G/H]`, isomorphic to `Q[G] e_H`, where

    e_H = (1/|H|) sum_{h in H} h.

Its Hilbert completion is `ell^2(G/H)`, a summand of `ell^2(G)` of
von Neumann dimension `1/|H|`. Therefore `H_n` is a finite sum of these
summands and has dimension `b_n`. In particular `dim_G H_0=q-1`.

Any `Q[G]`-linear map between two finite orbit modules is represented,
using these projective summands, by a finite matrix of finite group-ring
sums. It consequently extends to a bounded map between the completions.
The same is true of the coordinate projection from a larger orbit module
onto a smaller one. This argument is only used at **finite** depths.

For a bounded equivariant map `B` between finite Hilbert `G`-modules,
write `rank_G B=dim_G closure(im B)`. Polar decomposition identifies the
support projections of `B*B` and `BB*`, so they have equal finite trace.
Consequently rank is additive for block diagonal sums, is zero exactly
when `B=0`, and satisfies

    rank_G(CB) <= rank_G B,       rank_G(CB) <= rank_G C.

The first inequality also follows by restricting `C` to the closed image
of `B`. Positivity uses faithfulness of the trace. These are standard finite
von Neumann dimension facts; see Reich, [*Group von Neumann Algebras and
Related Algebras*](https://www.mi.fu-berlin.de/math/groups/top/members/publ/diss.pdf),
Chapter 3, especially Section 3.1. No flatness over `Q[G]` is invoked.

## 3. Why the defect seed detects nonsurjectivity

From `TS=I`, calculation gives

    E^2=E,       TE=0,       ES=0.

If `tau sigma=id`, then `E=0` and `delta=0`.
Conversely, if `delta=0`, faithfulness implies that `theta=0`. Thus, for
each one-site `psi_i`, the local function

    psi_i - psi_i o tau o sigma

is constant. It is zero on the nonempty set `tau(A^G)`, because
`tau sigma tau=tau`. That constant is therefore zero. The one-site basis
separates symbols, and translation gives the same conclusion at every
coordinate. Hence `tau sigma=id` on the full shift.

This also shows directly why passing to observables modulo constants
does not lose a genuine range defect. Finally, under `sigma tau=id`,
surjectivity of `tau` is equivalent to `tau sigma=id`.

## 4. Exact recovery of arbitrarily many defect copies

For `i,j>=0`, the identity `TS=I` cancels the middle powers. Using
`T theta=0`, `E theta=theta`, and `ES=0`, one obtains

    E T^i S^j theta = theta   if i=j,
                      0      if i!=j.                 (1)

For completeness: if `i<j`, cancellation leaves `E S^(j-i) theta=0`;
if `i>j`, it leaves `E T^(i-j) theta=0`; equality of indices leaves
`E theta=theta`. There is no commutation of `S` and `T` in this calculation.

Fix `n>=1`. On the algebraic modules define

    Phi_n:(P_0)^n -> P_(n+1),
    Phi_n(v_0,...,v_(n-1)) = sum_{j=0}^{n-1} S^j theta(v_j).

Each summand is in `V_(j+2)`, so the whole image lies in `V_(n+1)`.
Let `pi_2` be projection onto the basis orbits of `P_2`, inside any larger
`P_k`. Define

    Psi_n:P_(n+1) -> (P_2)^n,
    (Psi_n z)_i = pi_2 E T^i z,       0<=i<n.

This is a finite composition: `E T^i P_(n+1)` lies in `P_(n+i+3)`,
before applying `pi_2`. Section 2 therefore supplies bounded extensions
of both `Phi_n` and `Psi_n`. Equation (1) implies

    Psi_n Phi_n = diag(theta,...,theta).               (2)

Conversely, let `B_n:(P_2)^n -> P_(n+1)` be
`B_n(z_0,...,z_(n-1))=sum_j S^j z_j`. It too is bounded after completion,
and

    Phi_n = B_n diag(theta,...,theta).                 (3)

The identities extend from dense algebraic subspaces to these finite
Hilbert modules. Rank monotonicity in (2) and (3) now gives, in both
directions,

    n delta <= rank_G Phi_n <= n delta.

Thus `rank_G Phi_n=n delta`. Its closed image is contained in the closed
image of `V_(n+1)`, proving the stated lower bound.

This avoids a tempting invalid argument: independent algebraic submodules
need not have independent Hilbert closures. The two explicit bounded
factorizations, not algebraic independence, establish equality of ranks.
No bound uniform in `n` on `Phi_n` or `Psi_n` is needed, and no globally
bounded extension of `T` or `S` on the entire observable completion is assumed.

If `tau` were nonsurjective, Section 3 would give `delta>0` and hence
`liminf d_n/n>=delta`. This proves the sublinear criterion and its weighted
orbit-count version. Finite pattern-orbit closure makes `b_n` bounded,
recovering the earlier repository theorem.

## 5. Existence of the local decoder

An injective continuous map `tau` from the compact full shift into itself
is a homeomorphism onto its closed image `Y`. The inverse coordinate at
the identity is continuous and finite-valued. Each point of `Y` has a
relative cylinder neighborhood on which this coordinate is constant;
compactness gives finitely many such cylinders. Their finite coordinate
sets have finite union `N`, so equality on `N` determines the inverse
coordinate throughout `Y`.

Define the decoder's local rule on occurring `N`-patterns by that inverse
coordinate, and assign any alphabet value on the remaining patterns.
Translate the rule to all coordinates. Equivariance of the inverse on
`Y` gives a cellular automaton `sigma` on the entire full shift with
`sigma tau=id`. This proves the assertion without extending the inverse
as a global inverse. It works for arbitrary, including uncountable, `G`.

## 6. A reversible automaton has exactly linear growth

Take `G=Z`, `A=F_2^2`, and the rational Walsh basis

    1, alpha_j=(-1)^(a_j), beta_j=(-1)^(b_j), alpha_j beta_j.

The automaton and its inverse are

    tau(a,b)_j   = (a_j XOR b_j,     b_(j+1)),
    sigma(a,b)_j = (a_j XOR b_(j-1), b_(j-1)).

Substitution verifies both compositions are identity. On Walsh monomials,

    T alpha_j=alpha_j beta_j,     T beta_j=beta_(j+1),
    S alpha_j=alpha_j beta_(j-1), S beta_j=beta_(j-1).

For every integer `k`, put `m_k=T^k alpha_0`, interpreting negative powers
using `S=T^(-1)`. Explicitly,

    m_k = alpha_0 product_{j=0}^{k-1} beta_j       (k>=0),
    m_k = alpha_0 product_{j=k}^{-1} beta_j       (k<0).

The empty product gives `m_0=alpha_0`; also `m_1=alpha_0 beta_0`.
The identity `T^k beta_0=beta_k` shows that every iterate of a one-site
basis vector is in one of the translation orbits

    beta_0,       m_k for -n<=k<=n+1.                (4)

Conversely every orbit in (4) is generated at depth at most `n` from
`beta_0,m_0,m_1`. Since `T` and `S` are inverses, every word of length
at most `n` is a power with exponent between `-n` and `n`. The list (4)
therefore describes `V_n` exactly, not merely a lower bound.

These orbits are distinct. The unique `alpha` occurrence fixes the anchor
of an `m_k`; their sets of `beta` positions distinguish every integer `k`.
The `beta_0` orbit has no `alpha` occurrence. Distinct Walsh monomials are
basis vectors, so there are no additional linear dependencies. All finite
nonempty patterns in `Z` have trivial translation stabilizer. It follows
that

    d_n=b_n=1+(2n+2)=2n+3       for every n>=0,
    delta=0.

Thus linear observable growth is compatible with complete reversibility.
The inverse of a bijection is unique, so choosing a different local decoder
does not repair the failed sublinear hypothesis for this automaton. In
particular, the new criterion is sufficient, not necessary. The raw number
of saturated pattern orbits would also be an inadequate novelty claim:
any nonstabilizing saturation adds at least one orbit per step anyway.
The theorem's actual content is the exact Hilbert rank of the defect tower
and its bound on the **unsaturated** observable span.

## 7. Research boundary and replay scope

The rank calculation is a finite-trace version of the standard defect
matrix-unit calculation for a one-sided inverse. The earlier finite-orbit
criterion and the reversible example are already in this repository.
The quantitative refinement and the exact `2n+3` count were derived here;
the searches recorded in the session note do not establish external novelty.

There is no argument here that forces `delta=0` for an arbitrary automaton.
A universal assertion of sublinear `d_n` is false by Section 6. A proof of
Gottschalk by this approach would need an additional invariant or estimate
that kills the defect while permitting the reversible growth in (4).
Finite trace on each window is insufficient because the windows grow.

The companion `check-gottschalk-observable-growth-2026-09-07.py` replays
integer polynomial identities in the relation `TS=I`, compares them with
the action on finitely supported vectors indexed by the infinite set `N`,
and enumerates the Walsh orbit closure through its specified depth. It
does not search all cellular automata, approximate an unknown group, test
von Neumann dimensions numerically, or verify the theorem in Lean.
