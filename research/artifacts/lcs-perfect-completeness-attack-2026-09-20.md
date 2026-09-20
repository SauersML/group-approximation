# A global zero-noise counterexample to the TV decoder

Date checked: 2026-09-20. Scope: perfect **quantum** completeness with
uniform soundness, not the weaker perfect-commuting compiler now supplied
by a fixed separating LCS.

## Source boundary

Primary source: Taller--Vidick, [arXiv:2507.22444v2](https://arxiv.org/html/2507.22444v2).
The HTML proof itself was read, including Definitions 3.2 and 4.1,
Proposition 4.1, Lemma 4.2 and Theorem 5.2. In Proposition 4.1, after
equation (7), the decoder's inverse-degree factor is compared with the
noise multiplier. Lemma 4.2, equations (9)--(11), loses completeness at
the honest atom's mask value. Thus deleting the noise restores honest
completeness but removes the stated decoder estimate. The projection
comparison is Lemma 2.6; parallel repetition is Theorem 2.4, citing
Dinur--Steurer--Vidick, [arXiv:1310.4113](https://arxiv.org/abs/1310.4113).

The result below is a direct counterexample calculation, not a theorem
claimed from that paper. It shows that replacing the final inequality alone
cannot fix a generic zero-noise reduction.

## 1. An explicit gapped synchronous source

Let G have questions i,j in {1,2,3,4}, sampled independently and uniformly,
and answers a,b in {0,1,2}. Accept precisely when

    i=j and a=b, or i!=j and a!=b.                         (1)

This is the three-colouring game of K4. Every question pair has a nonempty
winning relation. We prove, for arbitrary finite-dimensional strategies,

    omega_q(G) <= 11/12.                                 (2)

Use projective measurements, after local Naimark dilation, and a unit
state psi. Set

    x_ia=(A_i^a tensor I)psi,
    y_ia=(I tensor B_i^a)psi,
    c_ia=(x_ia+y_ia)/2,  d_ia=(x_ia-y_ia)/2.

Let D=sum_i P[a!=b | i,i] and O=sum_(i!=j) P[a=b | i,j].
The overall loss is (D+O)/16. Completeness of each measurement gives

    sum_a x_ia=sum_a y_ia=psi,
    sum_(i,a) ||d_ia||^2=D/2.                            (3)

The second identity follows from
sum_a ||x_ia-y_ia||^2=2 P[a!=b | i,i]. Put
C_a=sum_i c_ia and D_a=sum_i d_ia. Then

    sum_a ||C_a||^2 >= (1/3)||sum_a C_a||^2=16/3,
    sum_a ||D_a||^2 <= 4 sum_(i,a)||d_ia||^2=2D.          (4)

The total same-answer mass over all sixteen pairs is

    sum_(i,j,a) P[a=b=a | i,j]
      = Re sum_a <sum_i x_ia, sum_j y_ja>
      = sum_a (||C_a||^2-||D_a||^2)
      >= 16/3-2D.                                       (5)

Its diagonal part is 4-D. Therefore O>=4/3-D, so D+O>=4/3,
which proves (2). No dimension bound or synchronous-strategy restriction
was used.

Let B,pi be the constraint system and projection distribution obtained
from G by TV Definition 3.2. Encode the three colours by three distinct
two-bit strings; the unused fourth string is disallowed. Write
P=G(B,pi)=G^proj. The source's projection comparison and repetition theorem
give

    omega_q(P) <= sqrt(23/24)<1,
    omega_q(P^tensor-u) -> 0 as u -> infinity.             (6)

## 2. Supports that are globally compatible with actual TV queries

Fix the colour cycle sigma=(0 1 2). For each unordered pair i<j, choose
the following three allowed assignments of the two vertex blocks:

    T_{ij}={(a,sigma(a)):a in {0,1,2}}.                   (7)

The coordinates in (7) are in vertex order, not the orientation of the
sampled pair. For a diagonal pair use T_{ii}={0,1,2} on its one vertex
block. Each T has odd cardinality three, satisfies its context, and
projects bijectively to all three colours at either endpoint.

For a repeated outer context W, take the Cartesian product T_W of these
sets over its u distinct copies. For a repeated endpoint query U, let
T_U consist of all 3^u assignments of valid colours. Thus

    |T_W|=|T_U|=3^u, and restriction T_W -> T_U
    is a bijection for every supported pair (W,U).        (8)

These definitions are indexed by the actual Boolean variable sets.
For this source W determines, in each copy, an unordered vertex pair or
a singleton and hence determines both C and T_W. Reversing the sampled
pair changes neither. If W is also an endpoint query U, every coordinate
is a singleton and the two definitions agree. This handles query
identifications across contexts; it is not an invocation of the refuted
unrestricted odd-subset relaxation theorem.

## 3. A perfect scalar solution for every repetition count

For any raw Bob query (V,h), whether it arises in the U role or the W role,
give the answer

    z_(V,h)=product_(t in T_V) h(t).                     (9)

For U folding, h=f_U and f=m_f f_U pointwise. Since |T_U| is odd,

    z_(U,f_U)=m_f product_(t in T_U) f(t).               (10)

For W folding and conditioning, h=s_{g,C}. On T_W subset C this function
equals m_{g,C}g. Consequently

    z_(W,s_{g,C})=m_{g,C} product_(t in T_W) g(t).        (11)

At zero noise g'=f^up g. Multiplying (10), (11), and its g' version,
the factor from g appears twice and cancels. The remaining unsigned
factor is

    product_(t in T_U) f(t)
      product_(t in T_W) f(t|_U)=1,                     (12)

by the bijection (8). The right-hand side of the raw LCS equation is
exactly m_f m_{g,C} m_{g',C}, so every equation holds. Alice returns the
three values of the fixed assignment (9), and Bob returns its queried
value. Hence, for every u>=1,

    omega_classical(L^0(u,B,pi))=1.                     (13)

Repeated occurrences of a variable cause no problem because (9) is a
single assignment on the raw query set, and the parity verification
already respects their multiplicities.

## 4. Consequences and exact limits

For every eta>0, (6) supplies u with omega_q(P^tensor-u)<eta, while
(13) is still perfect. Thus no lower bound

    omega_q(P^tensor-u) >= F(omega_q^s(L^0(u,B,pi)))

can hold uniformly for all eligible sources and u if F(1)>0. This rules
out **any** constant-success zero-noise decoder for the unchanged test,
not only independent uniform selection from Fourier supports.

The Fourier supports in this example have size 3^u. In each cell the
folded observables are the scalar characters chi_{T_U} and chi_{T_W}, so
their Fourier POVMs are point masses. TV's independent uniform selector
then wins the repeated source with probability exactly 3^{-u}, because
the restriction map in (8) is bijective. Its inverse-degree loss is
therefore attained on an actual global perfect strategy; it is not merely
an artefact of bounding an arbitrary local coefficient.

This does not refute perfect quantum completeness hardness. The example
need not belong to the particular machine-indexed source family in the
hardness theorem. It excludes a generic unchanged zero-noise inner test,
including a proof that hopes to recover soundness merely by increasing u.
A successful use of that inner test would require an additional,
source-specific property excluding these global odd-support matchings,
plus a robust operator decoder. A new test could instead change the
cross-context equations so that (9) no longer solves them, while proving
perfect quantum completeness separately.

Rich 2-to-1 perfect-completeness conjectures do not supply this missing
property by themselves: their usual completeness and soundness are
classical and concern a different outer alphabet/constraint family.
An actual quantum soundness and encoding theorem would still be needed.

## 5. Prior-art and verification scope

Repository duplicate search covered `taller-vidick-*`, zero-noise,
noiseless, odd-subset, derangement, matching and colouring terms in research
and notes. The nearest established results are the local cell theorem
`tv-zero-noise-cell-is-an-abelian-torsor` and the local gadget theorem
`lcs-parity-gadgets-preserve-odd-dictator-affine-hull`. Neither establishes
global compatibility or arbitrarily low quantum value of the repeated
source. The earlier universal `linear-encoding-lcs-admits-odd-subset-cheats`
was read together with its explicit refutation; the present argument
checks the specific TV equations directly.

External searches for the paper combined with zero noise, colouring, and
perfect completeness did not locate this exact worked counterexample.
No priority claim is made: odd-support long-code cheats are standard in
spirit, and (7)--(13) are an explicit audit witness for this repository.
The full TV HTML source was checked at the cited steps; source metadata
alone was not treated as verification. No computation, build, or search
exhaustion was run. The proof consists of the displayed finite identities
and the explicitly cited projection/repetition theorems.

Independent cross-review on 2026-09-20 by the root and the sibling
`lcs_hardness_audit` agent confirmed the unrestricted midpoint-vector
bound. The sibling additionally checked Definitions 3.2 and 4.1 against
the primary HTML, including reversed pairs, duplicated contexts,
U/W query collisions, odd-product folding, and the exact 3^{-u}
selector probability; no flaw was found. This is recorded review,
not a replacement for the displayed proof or a formal verification claim.
