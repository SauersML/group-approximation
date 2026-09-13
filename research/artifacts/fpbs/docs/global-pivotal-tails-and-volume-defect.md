# Global pivotal tails and the exact finite-volume defect

September 12, 2026. Written deductions, not a resolution of
Benjamini--Schramm or a claim of novelty. This strengthens the existing
[dangling-bridge lemma](relative-susceptibility-reduction.md#5-dangling-bridges-under-uniqueness-supporting-lemma)
and identifies precisely the missing expectation bound in its application
to the finite-ball pivotal route.

## 1. Inputs and status check

Let G be a connected nonamenable transitive graph of maximum degree d.
Fix p in (p_c,1) at which Bernoulli bond percolation has a unique infinite
cluster almost surely. Put

    theta = P_p(|C_o|=infinity),
    chi_f = E_p[|C_o|; |C_o|<infinity].

Hermon--Hutchcroft, [Theorem 1.1](https://arxiv.org/html/1904.10448#S1),
gives exponential tails for the size of a finite cluster at every fixed
p>p_c. In particular, for some a>0,

    M_a = E_p[|C_o| exp(a|C_o|); |C_o|<infinity] < infinity.       (1)

Their theorem is stated using the number of edges touching the cluster;
on a bounded-degree connected graph this also gives (1), after decreasing
a. No uniform estimate as p decreases to p_c is being imported.

The other input is the already established deletion-tolerance argument:
every bridge in the unique infinite cluster has exactly one infinite
side. The calculation below uses Bernoulli finite energy explicitly.

Checked on September 12, 2026: [Chu v2, Section 1.B, dated September 5](https://arxiv.org/html/2608.06644v2#S1.SS2)
still states the general nonamenable separation as conjectural. Searches
of this repository and the primary literature found the existing
qualitative dangling-bridge lemma and Hermon--Hutchcroft's more general
bridge-tree machinery. These are elementary consequences of those
inputs; neither the surgery method nor the tail conclusion is presented
as previously unknown in the literature. No computational claim is made.

## 2. An exact bridge-closing identity

For a vertex v in an infinite cluster, let D_v be the set of open edges e
such that closing e makes C_v finite. Write A_e(v) for that finite vertex
set in the modified configuration, and N_v=|D_v|. Set N_v=0 when C_v is
finite. This definition is meaningful even without uniqueness.

For a finite cluster C_v in the original configuration, let J_v count
the boundary edges whose other endpoint belongs to an infinite cluster.
All these boundary edges are closed. Then, for every nonnegative function
f on finite vertex sets containing v,

    E_p sum_(e in D_v) f(A_e(v))
      = p/(1-p) E_p[f(C_v) J_v; |C_v|<infinity].                (2)

**Proof.** Fix an edge e and all states other than its own. In the
configuration with e closed, its endpoints must belong to a finite
cluster containing v and an infinite cluster, respectively, for e to
contribute. Opening e then puts v in an infinite cluster and makes e a
bridge with finite side exactly that original C_v. Conversely, every
contribution on the left arises in this way. The two edge states have
probabilities p and 1-p, giving the identity for this e. Sum using
Tonelli; no summability assumption is needed. QED.

Since J_v<=d|C_v|, (2) implies

    E_p N_v <= d p chi_f/(1-p),                                (3)
    E_p #{e in D_v: |A_e(v)|>=m}
      <= d p/(1-p) E_p[|C_v|; m<=|C_v|<infinity].               (4)

This first-moment conclusion only needs finite truncated susceptibility,
which is already a Cairn input. It does not require differentiating an
infinite-volume connection event or identifying theta' with pivotals.

For completeness, the sets A_e(v), for e in D_v, are strictly nested.
Indeed, choose an infinite simple ray in the original locally finite
C_v starting at v. It crosses every e in D_v exactly once, since the
side containing v after deleting e is finite. Suppose it crosses e
before f. Then f is outside A_e(v), so the connected set A_e(v) remains
connected to v after deleting f, giving A_e(v) subset A_f(v). The ray
vertex immediately after e belongs to A_f(v) but not A_e(v), so the
containment is strict.
In particular N_v>=m entails that at least one such side has at least m
vertices. This last conclusion also holds when N_v is infinite, by
selecting any m of its edges. Consequently (1) and (4) give

    P_p(N_v>=m) <= d p M_a/(1-p) exp(-a m),   m>=1.             (5)

## 3. Uniform tails for global two-point pivotals

Let Z(v,w) be the number of open edges pivotal for global connection of
v to w, with Z(v,w)=0 when they are disconnected. At uniqueness,

    Z(v,w) <= N_v+N_w                    if |C_v|=infinity,
    Z(v,w) <= |C_v|-1                    if |C_v|<infinity.    (6)

The first assertion is the dangling-bridge lemma. For the second, each
pivotal belongs to every simple open v-to-w path, whose length is at
most |C_v|-1. Thus, uniformly in v,w,

    E_p Z(v,w) <= K_p := (1+2dp/(1-p)) chi_f.                  (7)

Moreover (1), (5), (6), and a union bound give constants A_p<infinity
and b_p>0 such that

    P_p(Z(v,w)>=m) <= A_p exp(-b_p m),   m>=1.                 (8)

For example one may take b_p=a/2 and
A_p=M_a(1+2dp/(1-p)): the finite-cluster contribution is at most
M_a exp(-a m), while each infinite-endpoint contribution is bounded
using N_v>=ceil(m/2). These constants are independent of the endpoints.

Uniqueness and FKG give P_p(v connected to w)>=theta^2. Dividing (7)
or (8) by theta^2 therefore bounds the conditional expectation and tail,
uniformly in the endpoints. In particular global pivotals have a
uniform exponential moment conditional on connection at each fixed
uniqueness parameter. The same statements hold after averaging w over
any independent random endpoint, including X_n.

The dependence on p matters. Neither K_p/theta^2 nor b_p is controlled
uniformly close to p_c. These conclusions do not imply the existing
uniform near-critical finite-ball pivotal budget.

## 4. The exact excess caused by a finite volume

Fix v,w and an increasing finite vertex exhaustion V_R containing them.
Let E_R mean connection in the induced open graph on V_R; let E mean
global connection. Let Z_R be its open pivotal count, set to zero on
E_R's complement, and let Z=Z(v,w). Define

    B_R = Z_R - Z 1_(E_R).                                   (9)

**Proposition.** B_R>=0, B_R tends to zero almost surely, and Z_R tends
to Z almost surely. At a fixed uniqueness parameter as above,

    E_p Z_R = E_p[Z 1_(E_R)] + E_p B_R,
    lim_R E_p[Z 1_(E_R)] = E_p Z.                            (10)

Consequently, as R tends to infinity,

    E_p[Z_R | E_R] -> E_p[Z | E]
       if and only if E_p B_R -> 0.                          (11)

Here the conditional expressions are used only for all sufficiently
large R, when their denominators are positive. Equivalently, (11)
holds exactly when the family {B_R} is uniformly integrable, and
exactly when the family {Z_R} is uniformly integrable.

**Proof.** On E_R, every global pivotal edge is in every v-to-w open
path, hence in every such path in V_R, and is a finite-volume pivotal.
This proves nonnegativity. If E fails, all Z_R and Z are zero. If E
holds, select one finite simple open path P. For all sufficiently large
R, P lies in V_R, so all finite-volume pivotals lie on this fixed path.
For every edge of P that is not a global pivotal, choose a finite open
v-to-w bypass avoiding it. There are only finitely many such edges and
bypasses. Eventually V_R contains all the bypasses, and precisely the
global pivotal edges remain pivotal in V_R. This proves eventual
equality, not just convergence, for each configuration.

Equation (10) is (9) in expectation; its limit follows by monotone
convergence or domination by the integrable Z from (7). Also
P_p(E_R) increases to P_p(E)>0. Divide (10) by P_p(E_R) to obtain
(11). For nonnegative variables converging almost surely to zero,
convergence of means to zero is equivalent to uniform integrability.
Finally Z 1_(E_R) is dominated by integrable Z, so adding or removing
it preserves uniform integrability. QED.

This proposition does not claim that the random stabilization radius
has a controlled tail. B_R counts precisely the pivotal edges which
have an open bypass globally but no such bypass within V_R. Each
chosen bypass for a counted edge must leave V_R. Almost-sure eventual
stabilization cannot replace the missing uniform-integrability bound.

## 5. Consequence for the live finite-ball route

For fixed n and R>=n take v=o, w=X_n, V_R=B_G(o,R). The walk has finite
support for fixed n, so the preceding proof and its integrability bounds
apply after averaging over X_n. The exact split is

    E_p[Z_R | E_R]
      = E_p[Z(o,X_n) 1_(E_R)]/P_p(E_R)
        + E_p B_R/P_p(E_R).                                (12)

Thus the qualitative dangling-bridge lemma can now be replaced by a
proved uniform global pivotal tail at each fixed uniqueness parameter.
The finite-volume issue is isolated as the second nonnegative term,
and (11) is a necessary and sufficient criterion for passing its mean
to infinite volume at fixed p,n. This is an actual strengthening of
the reusable input, not a proof that the criterion holds.

The existing OPEN target `fpbs-universal-subcritical-pivotal-growth-rate`
takes a supremum over every R>=n and p arbitrarily close to p_c. Neither
the fixed-p tail constants in (8) nor the almost-sure stabilization in
Section 4 controls that supremum. Even under hypothetical p_c=p_u, two
issues remain: degeneration of the global tail constants as p decreases
to p_c, and the mean boundary-bypass excess at the required finite
volumes. The exponential spike theorem allows p and R to vary with n,
so it cannot be contradicted by (7), (8), or (11).

No new sufficient hypothesis is inserted simply by renaming these
uncontrolled quantities, and no route claims that this proves threshold
separation. Cairn records the strengthened tail theorem and exact volume
defect, with dependencies on the existing finite-susceptibility and
dangling-bridge inputs. Their use is to make the unfinished estimate in
the existing pivotal route more specific.
