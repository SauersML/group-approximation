# Sparse base surgery from infinitesimal containment and separator descent

September 10, 2026. A written deduction combining cited theorems. No novelty,
independent mathematical verification, or solution of Fixed Price is claimed.
The new inputs close a specific coupling-to-base separator gap. They do not
construct a universally cost-preserving descent of generating graphings.

## 1. Inputs and their precise scope

[F] Fraczyk, *Infinitesimal containment and sparse factors of iid*,
arXiv:2512.09301v1, Definition 1.8 and Theorems 1.9 and 3.10:
<https://arxiv.org/html/2512.09301v1#S1.SS3>.
For an exact countable group, a finite set S and epsilon>0, there are
delta>0 and k<infinity such that every FIID vertex set of density at most
delta can, in an invariant random coupling, have an epsilon proportion
of its vertices removed, leaving S-components of size at most k.

The coupling is not asserted to be a factor of the original labels.
The quantifiers fix S and epsilon BEFORE delta and k. The general
infinitesimal-containment theorem, Theorem 1.6, concerns Bernoulli to
regular containment; it does not assert that arbitrary source processes
can be copied into Bernoulli. Exactness is needed for Theorem 1.9.

Theorem 3.10 already removes the extra randomness for an essentially
free action: an (S,k,epsilon)-hyperfinite region U admits a measurable
vertex cut of relative measure at most -11|S| epsilon log(epsilon),
with the same component bound k. Thus the coupling-to-base step is
available in this paper itself, not a new result of this note.

[L] Lovasz, *Hyperfinite graphings and combinatorial optimization*,
arXiv:1709.03179v2, Theorems 11--12 and Corollary 13:
<https://arxiv.org/pdf/1709.03179>.
Fractional k-separation is invariant under local equivalence. Actual
k-separation is at most the fractional value times a logarithmic factor
depending on the maximum degree and the fractional value, NOT on k.
Corollary 13 gives sep_k(G2)<=sep_k(G1) log_2(8d/sep_k(G1)) for locally
equivalent bounded-degree graphings. We use only that this upper bound
tends to zero with sep_k(G1), uniformly in k. Directed edge measure in
Section 1.2 of [L] counts both orientations; our c(F) counts an edge once.
Using the larger directed measure throughout gives a safe upper bound
for c(F), independently of that normalization convention.

[M] Berczi--Imolay--Schweitzer, *Measurable Matroids: Foundations and
Min--Max Theorems*, arXiv:2608.16464v1, Theorem 7.20 and Remark 7.18:
<https://arxiv.org/html/2608.16464v1#S7.SS4>.
The approximate basis-exchange theorem is a further available tool.
For the cycle matroid its bases are hyperfinite essential forests,
not necessarily connected spanning subgraphs of each orbit. Remark 7.18
explicitly distinguishes rank from optimized cost. We do NOT use this
theorem as an orbit-connectivity theorem. The surgery below uses actual
finite components and their spanning trees to retain connectivity.

## 2. The random cut can be replaced by a base-measurable edge cut

Let Gamma be an exact countably infinite group, let X be a nontrivial
Bernoulli action with its probability measure mu, and fix a finite
symmetric S not containing the identity. Work on its free invariant
conull part. Let H be any simple Borel subgraph of the S-Cayley graphing;
in particular its degree is at most d=|S|. It need not generate here.
All graphing statements are modulo invariant null sets. If S is empty,
the edge assertions are immediate; below assume d>=1.

**Theorem A.** For every eta>0 there exist delta>0 and k<infinity such
that, whenever A is a Borel subset of X with mu(A)<=delta, there is a
Borel edge set F contained in H[A] such that

    c(F)<=eta mu(A),
    every component of H[A] minus F has size at most k.       (1)

Null A is immediate with F empty. The inequality is strict when
a=mu(A)>0. In that case apply [F] to the FIID subset
{g:g^(-1)x in A}. Its invariant coupling with the deleted set can be
joined to X over the FIID subset map, by disintegration. This gives a
standard pmp extension Y->X with a marked vertex set C contained in
the lift of A and nu(C)<=epsilon a. Freeness of X makes the factor
orbitwise bijective, including on the induced subgraph H[A].

Normalize both A and its lift by a. The base graphing H[A] and its
lift on Y are locally equivalent probability graphings of degree at
most d. Removing all edges incident to C upstairs leaves components of
size at most k (and isolated deleted vertices). Its directed edge
measure is at most 2d epsilon in the normalized probability space.

Choose epsilon so small that 2d epsilon<1 and

    (2d epsilon) log_2(8d/(2d epsilon)) < eta/2.

Corollary 13 of [L], using monotonicity of its bound on this small
interval, gives sep_k(H[A])<eta/2. Take a Borel cut within eta/2 of
that infimum, then undo the normalization by a. This proves (1).
The k is exactly the finite component bound provided after choosing
epsilon; no k^2 factor or assumption of attainment is used.

This constructs the cut on X itself. It does not assume that the
particular random cut from [F] can be copied to X. This argument passes
through fractional separators and their measurable rounding.

**Direct alternative already in [F].** Theorem 3.10 gives V contained
in A with mu(V)<=-11d epsilon log(epsilon) mu(A), and S-components
of A minus V of size at most k. Remove the H[A] edges incident to V.
Their cost is at most d mu(V), and the V vertices become isolated.
Choose epsilon with -11d^2 epsilon log(epsilon)<eta. This proves
Theorem A directly from Theorems 1.9 and 3.10. The Lovasz argument
above records an alternative general graphing interface, not a
necessary new ingredient or a claim of priority for separator descent.

## 3. A connected replacement on the original action

Suppose in addition H generates the full orbit relation. Choose F as
in (1). On each finite component of H[A] minus F choose a spanning
tree measurably: order the finitely many candidate edge sets using
a fixed Borel ordering and select the first spanning tree. Retain
these trees, every F edge, and all H edges outside H[A]. Call the result J.

Every deleted edge has endpoints in one of the finite components and
therefore has a path in its retained tree. Thus J generates exactly
the same relation as H. It is a base-measurable subgraphing of H.
If k_A(x) is the size of the finite component at x in A, then

    c(J intersect H[A])
       <= mu(A)-integral_A 1/k_A(x) dmu(x)+c(F)
       <= (1+eta)mu(A).                                  (2)

Consequently

    c(J)<=c(H)-c(H[A])+(1+eta)mu(A).                      (3)

These are genuine connected replacements, not an inference from
essential spanning forests. They use an actual finite partition
with a small paid edge boundary on the original action.

## 4. A trace saving when the relative certificate is supported there

Use the edge Hilbert modules and finite trace from
`relative-cycle-exchange.md`. Let 0<=K<=P_Z(H) be a positive contraction
whose range is supported on edges with both endpoints in A. It may,
in particular, be the relative operator of a free source factor inside
the lift of H, provided that support hypothesis holds.

**Theorem B.** The same J satisfies

    c(J)<=c(H)-Tr(K)+eta mu(A).                           (4)

**Proof.** Let W be the closed submodule of ambient finite-cycle space
Z(H) consisting of chains supported on H[A]. Its vectors have zero
boundary, because the boundary operator is bounded and all finite
cycle chains have zero boundary. The range of K lies in W, so
Tr(K)<=dim W.

Project W to the F-edge coordinates. The dimension of its image
closure is at most c(F). Its kernel consists exactly of cycle chains
on the finite components of H[A] minus F. Indeed, a chain in this
kernel has zero boundary on every finite component, hence is a sum
of that component's finite cycles. Conversely those finite cycles
belong to Z(H). Call this kernel Z0. Finite-trace rank-nullity gives

    dim W <= dim Z0+c(F).

Replacing each finite component by a tree deletes edge measure
exactly dim Z0. Hence

    c(J)=c(H)-dim Z0 <= c(H)-Tr(K)+c(F),

which proves (4). This argument needs support, not an unsupported
replacement of small exterior trace by small exterior rank.

For a relative certificate with Tr(K)=c(H)-c(Phi), (4) gives

    C(X)<=c(Phi)+eta mu(A).                              (5)

This closes connected rounding under the stated sparse-support
hypothesis without the earlier block-size multiplier.

## 5. Why this is not universal Fixed Price

No theorem here constructs sparse base support for the relative
certificate of an arbitrary nearly optimal source graphing. The
existing rare reuse flags live upstairs; projecting a rare event
need not leave a rare support downstairs. Moreover, near-optimal
graphings may require a changing finite label set S. The delta in
Theorem A depends on S and eta. Choosing successively larger S
does not justify ignoring that dependence.

There is also a quantitative support budget: since H has degree at most d,

    Tr(K)<=dim ell^2(H[A])=c(H[A])<=d mu(A)/2.            (6)

For a fixed positive relative saving Delta=Tr(K), exact support therefore
requires mu(A)>=2 Delta/d. Sending the support measure to zero with a
fixed label set cannot remove a fixed positive gap in one application.
Increasing d changes the sparsity threshold in Theorem A. An iterative
scheme would need to justify its total saving, total cut cost, and
generation in the limit; none follows just from (4).

Small trace outside A would not suffice for the proof of Theorem B:
the dimension of the image of a coordinate projection can be large
even when the corresponding trace is small. No such substitution
is made. Nor does Theorem A apply to all groups: [F] expressly
requires exactness and discusses failure beyond that class.

The useful change is precise: invariant-coupling separators can now
be descended with a controlled loss, and a sparse-supported relative
cycle certificate can be rounded while preserving orbit connectivity.
Producing the support at source-optimal cost, handling nonexact groups,
and excluding mixed finite/infinite action costs remain unresolved.

## 6. Relation to the existing Cairn attempts

* `fpbs-sparse-reuse-signal-near-cost-one` supplies rare SOURCE flags,
  not the base support needed above.
* `fpbs-relative-cycle-operator-descent` supplies the trace identity;
  it does not supply sparse support for K.
* `fpbs-relative-cycle-block-rounding-bound` uses a small weighted
  boundary trace with a block-size penalty. Theorem B instead pays
  the rank of the actual cut; neither hypothesis implies the other
  in the general setup.
* `fpbs-cost-subgraph-rank-obstruction` still rules out treating
  optimized subrelation cost as a restriction-consistent matroid rank.
  The new measurable matroid theorem does not assert that identification.

These links record the actual mathematical interfaces. None is an
additional unproved premise silently declared established.

## 7. Cheap source separators cannot stand in for ambient separators

Theorem 3.10 of [F] controls the graph generated by the fixed S on
the region U. Its proof uses the full S-boundary of each finite piece:
every point in that boundary lies in the cut or outside U. If a source
graphing Phi omits some S-edges according to forgotten information,
its components have no such property relative to the ambient graph H.
An omitted S-edge can leave the component without touching its Phi-cut.
Freeness separates projected finite sets but does not remove these edges.

This distinction has a quantitative example even on one prescribed base
action of a group whose fixed price is already known. Let Gamma=F_2 x Z,
let a,b freely generate F_2, and let z generate the central Z. On any
essentially free pmp action let H be the product Cayley graphing.
Choose a complete section D_delta for the z-action with measure at most
delta. Keep all z-edges and the positive a- and b-edges starting in
D_delta; call this graphing Phi_delta. Centrality gives a path realizing
each a- or b-step by moving along z to D_delta, taking that step, and
returning along z. Thus Phi_delta generates and

    c(Phi_delta)=1+2 mu(D_delta)<=1+2 delta.              (7)

Delete its horizontal edges at cost at most 2 delta. By the Rokhlin
lemma for the aperiodic z-action, choose a height-N tower covering
measure at least 1-epsilon. Keep only its internal vertical edges.
The resulting components have size at most N, with all points outside
the tower isolated. The additional cut cost is at most 1/N+epsilon:
if B is the tower base, it equals 1-(N-1)mu(B). Consequently these
generating Phi_delta admit bounded finite pieces with cut cost tending
to zero as delta,epsilon tend to zero and N tends to infinity.

In contrast, every finite nonempty vertex set A in T_4 x Z has at
least 2|A| horizontal boundary edges. On each nonempty horizontal
layer, the induced finite forest has at most |A_layer|-1 edges, so
its horizontal boundary is at least 2|A_layer|+2. Sum over layers.
For any measurable partition into finite orbit subsets P_x, the pmp
mass-transport identity therefore gives

    c(H edges crossing the partition)
       = (1/2) integral |boundary_H P_x|/|P_x| dmu(x)
       >= 1.                                           (8)

In particular every H-cut leaving finite components costs at least
one, regardless of their size bound. Applying (8) to the components
of a proposed cut proves this even if it also deletes internal edges.

Thus there is no bound tending to zero that converts the separator
cost of an arbitrary generating subgraphing Phi into the separator
cost of its ambient H. Equations (7)--(8) already rule it out with
fixed degree and fixed labels; changing labels is not needed for this
failure. Small complete sections and the same cost-one construction
are also recorded in [the cost-rank note](cost-rank-duality.md).

This is an elementary scope check, not a new fixed-price obstruction.
Both actions can even be the same action in this example. It rules
out substituting a cheap source boundary for the ambient boundary in
Theorem A. A cost-preserving construction that also changes the base
graphing remains possible in principle and unproved in general.
