# Base-oblivious certificates never localize their relative cycle surplus

September 17, 2026. Written deductions over the established relative
operator descent (`fpbs-relative-cycle-operator-descent`) and the
established cost--Betti cycle identity
(`fpbs-graphing-cost-betti-cycle-dimension-identity`). Fixed price is not
resolved. No priority is claimed.

## 0. Setting and what is killed

Let Gamma be an infinite finitely generated group and pi:(Y,nu)->(X,mu) a
free p.m.p. factor. A finite-label source graphing Phi on Y has a finite
set S of group labels, with one representative from each pair
{s,s^{-1}}. For s in S let A_s be the set of y whose edge {y,s.y} lies
in Phi. Disintegrate nu = integral nu_x dmu(x) and put

    p_s(x) = nu_x(A_s),   p_e(x) = p_s(x') for the s-edge e={x',s.x'}.

The conditional-support graphing H keeps the base edge e exactly when
p_e>0. K is the averaged relative cycle operator of
`fpbs-relative-cycle-operator-descent`:
K_x = integral (P_Z(pi*H) - P_Z(Phi_y)) dnu_x(y), with Tr K = c(H)-c(Phi).
For an edge e of H write the **cycle weight**

    rho_G(e) = ||P_Z(G) delta_e||^2,

the squared norm of the projection of the unit edge vector onto the
closed span of finite cycles of G (zero when e is not an edge of G).

**Definition (base-oblivious certificate).** Phi is base-oblivious when
every p_s is mu-a.e. constant. The main example is the lift of a finite-label
graphing Psi of a free action a to the diagonal product Y = a x b, projected
onto X = b. Its occupancy of the s-edge at y=(omega,x) depends only on omega,
so p_s = mu_a(dom of label s in Psi). These are exactly the
graphings that witness C(a x b) <= C(a) in the conditional route
`fpbs-bernoulli-lower-bound-from-block-localization`.

**Invariant.** For a base-oblivious Phi with every p_s>0, H is the
Cayley graphing Cay(Gamma,S) on every orbit, and rho_H(s-edge)=rho_s
depends only on the label. Define the *diffuse cycle weight*

    D(Phi) = sum over s in S of infinite order of (1-p_s) rho_s.

**Where every member dies.** It dies at premise (14) of Theorem 6.1 of
`relative-cycle-exchange.md`, the displayed estimate of
`fpbs-relative-cycle-block-localization`. For every measurable partition
into blocks of size at most M, H-connected or not,

    (1+2 d M^2) Tr(P_out K) >= 2 d M D(Phi).

For torsion-free, non-cyclic Gamma with beta_1^(2)(Gamma)=0 and
c(Phi)<4/3, D(Phi)>=1/12, so the left side is at least 2/3 uniformly.

## 1. Lemma A: exact diagonal split of the relative operator

For every factor, finite-label generating Phi, base point x and edge e
of H in the orbit of x,

    <K_x delta_e, delta_e>
       = (1-p_e(x)) rho_H(e)
         + integral 1[e in Phi_y] (rho_H(e) - rho_Phi_y(e)) dnu_x(y),   (A)

and both terms are nonnegative.

*Proof.* K_x is defined as the weak integral of Q_y = P_Z(H) - P_Z(Phi_y).
Freeness identifies the orbit of y with the orbit of x, and pi*H with
H. So the diagonal coefficient is the integral of
<Q_y delta_e,delta_e> = rho_H(e) - ||P_Z(Phi_y) delta_e||^2. If e is
not an edge of Phi_y, every finite cycle chain of Phi_y vanishes at
the coordinate e, and so does every element of their closed span. Then
P_Z(Phi_y) delta_e = 0. If e is an edge of Phi_y, the finite cycles of
Phi_y are finite cycles of H. So Z(Phi_y) is a closed subspace of Z(H), and
||P_Z(Phi_y) delta_e||^2 <= rho_H(e). Integrating
rho_H(e) - 1[e in Phi_y] ||P_Z(Phi_y)delta_e||^2 against nu_x, with
nu_x{e in Phi_y} = p_e(x), gives (A). QED.

The first term is the **absence term**: an edge that has cycle weight in
H but is often missing from the source. The second is the **cycle-loss
term**: an edge that is present but lies on fewer source cycles. The
identity uses no resistance theory, only the nesting of cycle spaces.

**Consequence for every certificate.** Localization (14) requires

    (1+2 d M^2) integral over crossing edges of (1-p_e) rho_H(e) -> 0.

On block boundaries, the source occupancy of every edge with
non-negligible cycle weight in H must therefore be almost determined by
the base point. This is a necessary condition, not a construction.

## 2. Lemma B: forced crossing density along infinite-order labels

Let E be any measurable orbit partition into blocks of at most M
vertices. Let s have infinite order and W_s = {x : x and s.x lie in
different blocks}. Then mu(W_s) >= 1/M.

*Proof.* The action is free and s has infinite order, so
x, s.x, ..., s^M.x are M+1 distinct points of one orbit. They cannot all
lie in one block, so some k in {0,...,M-1} has s^k.x in W_s. Hence
sum_{k<M} 1_{W_s}(s^k.x) >= 1 everywhere. Integrate and use invariance
of mu. QED.

## 3. Lemma C: cycle-weight budget of a Cayley graphing

Let S generate Gamma, and let H = Cay(Gamma,S) be the graphing of a free
action, with degree 2|S| when Gamma is torsion-free. Put w_s = 1 when
s != s^{-1} and w_s = 1/2 otherwise. Then

    sum_s w_s rho_s = |S|_w - 1 - beta_1^(2)(Gamma),  and          (C1)
    rho_s <= 1 - 1/deg(H)  for every label s.                    (C2)

*Proof.* (C1): the normalized trace of P_Z(H) is the incident-edge
average (1/2) integral sum_{e at x} rho_H(e) = sum_s w_s rho_s. Here the
two s-edges at x have the same weight because right translation is a
Cayley graph automorphism. By the established
`fpbs-graphing-cost-betti-cycle-dimension-identity` this trace is
z(H) = c(H) - 1 - beta_1, and c(H) = |S|_w. (C2): the star chain u at an
endpoint x of e, which is +-1 on the edges at x, is orthogonal to every
finite cycle chain because a cycle has net flow zero at x. So u is
orthogonal to Z(H) and
||(I-P_Z)delta_e||^2 >= <delta_e,u>^2/||u||^2 = 1/deg(x). QED.

## 4. Theorem B: base-oblivious certificates pay the diffuse cycle weight

Let Phi be a base-oblivious finite-label generating graphing on Y. Let S
be its labels with p_s>0, so S generates Gamma and H = Cay(Gamma,S).
Let d >= deg H = 2|S|_w. Then for every measurable partition E into blocks
of at most M vertices,

    Tr(P_out K) >= D(Phi)/M,   (1+2 d M^2) Tr(P_out K) >= 2 d M D(Phi).   (B)

*Proof.* By the trace formula,
Tr(P_out K) = (1/2) integral sum_{e at x} 1[e crosses] <K_x delta_e,delta_e>.
For a label s let F_s(x) = 1[{x,s.x} crosses] <K_x delta_e,delta_e> with
e={x,s.x}. The other s-edge at x is {s^{-1}.x,x}. K is equivariant, so the
operators at x and at s^{-1}.x agree, and crossing status depends only on
the orbit partition. So this edge contributes F_s(s^{-1}.x), and invariance
of mu gives Tr(P_out K) = sum_s integral F_s dmu. (An involution has a single
edge at x, which carries weight 1/2 in the trace; its F_s is nonnegative
and is simply discarded below.) Every F_s >= 0 because K >= 0. For s of
infinite order, Lemma A with p_e = p_s and rho_H(e) = rho_s gives
F_s >= (1-p_s) rho_s 1_{W_s}. Lemma B gives integral F_s >= (1-p_s) rho_s / M.
Summing proves the first inequality, and 1+2dM^2 >= 2dM^2 proves the second.
QED.

Nothing about the blocks was used beyond their size. The kill therefore
covers H-connected blocks, block trees with one bridge per pair, and any
other finite-block scheme scored by the weighted boundary b(K,E).

## 5. Corollary C: a uniform kill below cost 4/3 when beta_1 = 0

Let Gamma be torsion-free, not cyclic, with beta_1^(2)(Gamma)=0. Let Phi
be a base-oblivious finite-label generating graphing of any free factor
Y->X with c(Phi) < 4/3. Then D(Phi) >= 1/12, and for every finite-block
partition

    (1+2 d M^2) Tr(P_out K) >= 2/3.

*Proof.* Torsion-freeness gives w_s = 1, and every label has infinite
order. S generates the non-cyclic group Gamma, so |S| >= 2, c(H) = |S| and
deg H = 2|S| >= 4. By Fubini, c(Phi) = sum_s p_s. Let T = {s : p_s >= 2/3}.
Then (2/3)|T| <= c(Phi) < 4/3, so |T| <= 1. Every s outside T has
1-p_s > 1/3, and by (C1) and (C2),

    D(Phi) >= (1/3) sum_{s not in T} rho_s
           =  (1/3) (|S| - 1 - sum_{s in T} rho_s)
           >= (1/3) (|S| - 2 + 1/(2|S|)).

This is 1/12 for |S|=2 and at least 1/3 for |S|>=3. Theorem B gives
(1+2dM^2)Tr(P_out K) >= 2dM D >= 2*4*1*(1/12) = 2/3. QED.

In particular take any free action a of such a group with C(a) < 4/3, and
any free b. Every near-optimal lift of finite-label graphings of a to
a x b violates (14) by the fixed amount 2/3, for every choice of blocks,
along every sequence.

## 6. Calibration, and what the obstruction says about the route

*The class dies where the conclusion is true.* Gamma = Z^2 is torsion-free,
non-cyclic, has beta_1 = 0 and fixed price 1 (Gaboriau's notes, Theorem
2.20, cited in the target node). For a Bernoulli b and any free a, a
lifted base graphing of b of cost 1+eps is a source graphing with K = 0
that localizes with singleton blocks. But by Corollary C, every lift of
graphings of a of cost < 4/3 fails (14) by 2/3. The sharp value on Z^2 is
visible directly: with S={s_0,t}, p_{s_0}=1 and p_t=eps, every t-edge lies on a
commutation square, so rho_t >= 1/4 and D >= (1-eps)/4. So the failure is a
property of the certificate class, not of the group. The only
certificates that can localize put base information into the occupancy of
boundary edges.

*What survives.* Lemma A is an identity for every certificate. A
localizing sequence must make (1-p_e(x)) rho_H(e) small on crossing
edges, in the (1+2dM^2)-weighted average. On the block boundary, source
occupancy must be almost a function of the base point, except on edges
of negligible cycle weight in H. The interior may stay random. Any
successful construction for `fpbs-relative-cycle-block-localization`
therefore has to solve a *boundary base-measurability* problem. It must
turn the source graphing, near its cost, into one whose boundary edges
are base-determined, and this is where all information about the
forgotten a-process has to be discarded. Oblivious averaging and lifting
from the independent factor do not do this.

*Robust form.* When p_s>0 a.e. but p_s is not constant, H is still
Cayley and the proof of Theorem B gives
integral F_s >= rho_s integral over W_s of (1-p_s(x)) dmu(x).
If mu{p_s > 1-eta} <= theta < 1/M, this is at least
rho_s eta (1/M - theta). So near-oblivious fully supported certificates
die in the same way unless their near-deterministic set for each
infinite-order label has measure comparable to 1/M. That set is where the
boundary must sit.

## Sources and certificate boundary

- `fpbs-relative-cycle-operator-descent` (established): definition,
  positivity and equivariance of K.
- `fpbs-graphing-cost-betti-cycle-dimension-identity` (established):
  z(H) = c(H) - 1 - beta_1 for bounded-degree generating graphings with
  infinite components.
- `relative-cycle-exchange.md`, Section 6: Theorem 6.1 and premise (14).
- Everything else above (Lemmas A, B, C2, Theorem B, Corollary C) is proved
  here from these inputs by elementary Hilbert-space and mass-transport
  arguments.
