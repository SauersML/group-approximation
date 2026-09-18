---
rg: 2
id: arithmetic-a5-near-group-not-fp-proof
kind: route
title: The arithmetic generators are tree automorphisms, the root-edge stabilizer is a union of virtually abelian level groups, and a finitely presented amalgam of such groups has bounded abelian rank
target: arithmetic-a5-near-group-is-not-finitely-presented
requires:
  - a5-free-product-has-simple-arithmetic-shell-envelope
  - a5-arithmetic-germs-embed-in-fp-odometer-host
  - a5-arithmetic-near-group-obeys-parity-charge-constraint
  - shell-germ-fp-is-an-ascending-hnn-gate
  - shell-fp-stabilizer-forces-fp-germ-group
artifacts:
  - experiments/shell-odometer-near-group-2026-09-17/odom.py
  - experiments/shell-odometer-near-group-2026-09-17/verify_abelian_rank.py
---

Notation. Put h=|A|-1 (h=59 for A_5). Index the nonidentity
elements of A by the digits 1..h, writing x_d for the element with
index d. Points of the Cantor set X are (r, d_1, d_2, ...), where r
in {0,1} is the root. The odometer a acts by

    a(d w) = (d+1) w   if d<h,
    a(h w) = 1 a(w).

A table leaf u -> v [k] means u w |-> v a^k(w). For a cone c, a_c
is the odometer acting on the tail below c and trivially elsewhere.
Composition is right to left.

**Step 0. The generators.** The enumeration nu=2q-1+epsilon puts the
first syllable in the least significant digit. So left multiplication
acts only on the first digit and on the root. This gives the
following tables, with carry 0 unless stated:

    lambda^(0)_x :  (1) -> (0, x);
                    (0, d) -> (0, x x_d)   if x x_d != 1,
                    (0, d) -> (1)          if x x_d = 1;
    lambda^(1)_x :  the same with the roots exchanged;
    s            :  (0) -> (1),  (1) -> (0) [carry 1].

These are the branches recorded in `a5-arithmetic-germs-embed-in-fp-odometer-host`:
- the lambda branches have source depth 1 and target depths 2, 1 or 0;
- s exchanges the roots, with a carry on the second root.

So G=<lambda(P), s> is the image of R_nu in B. As a model check,
`verify_abelian_rank.py` confirms the recorded mixed relation
[lambda_a s^(2h) lambda_a^-1, s^(2h^2)]=1 exactly, for A_5, C_4 and C_5.

**Step 1. G acts on a tree.** Let T have vertices (r, w) for r in
{0,1} and w a finite digit word, including the empty word. Its
edges are (0)—(1) and (r, w)—(r, w d). Every vertex has degree h+1.
The ends of T, seen from the edge e=(0)—(1), are exactly the points
of X.

Define vertex maps as follows:
- s: (0, w) -> (1, w) and (1, w) -> (0, a(w)). The odometer on a
  finite word is prefix-compatible, since a(w d) = a(w) d'. So s
  preserves adjacency, and it is a bijection.
- lambda^(0)_x:
  - (1, w) -> (0, x w) and (0) -> (0);
  - (0, d w) -> (0, (x x_d) w) when x x_d != 1;
  - (0, d w) -> (1, w) when x x_d = 1.

  This fixes (0), permutes its h+1 neighbours as x permutes A
  (with (1) standing for the identity), and carries each branch
  rigidly. It is an automorphism.
- lambda^(1)_x is defined symmetrically.

Each vertex map induces the boundary table of Step 0. Hence G <= Aut(T).
T is regular of degree at least 3, so an automorphism is determined by
its boundary action. The action on T is therefore faithful.

The action is edge-transitive. Let E be the G-orbit of e. If g e is in
E, then all edges at g(0) are g lambda^(0)(A) e, and all edges at g(1)
are g lambda^(1)(A) e. So E is closed under adjacency, and T is
connected, hence E is every edge. Moreover s swaps the endpoints of e.

Subdivide every edge at its midpoint m. Then G acts without inversions
on the subdivided tree, with one orbit of edges. Bass–Serre theory gives

    G = G_(0) *_(G_e+) G_m,

where G_e+ is the stabilizer of the oriented edge, i.e. of both (0)
and (1). G_(0) contains G_e+ with index at most h+1, and G_m contains
it with index at most 2.

**Step 2. Vertex stabilizers are locally virtually abelian.** For
D >= 0, let K_D be the set of elements of B with a table whose leaves
all have the form u -> v [k] with |u| = |v| = D. Here |u| counts digits
after the root. By the composition rule, (v -> y [j]) after
(u -> v [k]) is u -> y [j+k]. So K_D is a group, and

    L_D = { u -> u [k_u] } = Z^(2h^D)

is normal in K_D with finite quotient inside Sym(2h^D). Splitting a
depth-D leaf gives h depth-(D+1) leaves with equal source and target
depths. So K_D <= K_(D+1). Let K be the union of all K_D.

G_e+ <= K. Let g in G fix (0) and (1). Then g preserves each half-tree
and the distance to the root edge. Refine its table so that every
source cone has depth D, and let u -> v [k] be a leaf. g maps the cone
of the vertex (u) onto the cone of the vertex g(u), which also has
depth D. That cone is the set v a^k(X_tail), the cone of (v). So
|v| = D, and g is in K_D.

Every finitely generated subgroup of K lies in some K_D, so it is
virtually abelian. The same holds for G_(0) and G_m: a finitely
generated subgroup H meets G_e+ in a subgroup of index at most h+1,
which is again finitely generated.

**Step 3. G contains Z^infinity.**

*The power s^(2h).* s^2 is a on both roots, and a^h(d w) = d a(w).
So s^(2h) is the product of a_(r,d) over all depth-1 cones.

*Conjugating by lambda = lambda^(0)_x.* The conjugate
lambda a_c lambda^-1 of a localized odometer is a_(lambda c), whenever
lambda maps the cone c rigidly with carry 0. Let d_0 be the digit with
x x_(d_0) = 1. Then:
- the cones (0,d) with d != d_0 go to the depth-1 root-0 cones other
  than (0,x);
- the cone (0,d_0) goes to (1);
- each cone (1,d) goes to (0,x,d).

So lambda s^(2h) lambda^-1 is a product of localized odometers with
disjoint supports:
- a_(0,d') for the depth-1 root-0 cones other than (0,x);
- a_(1);
- the product over d of a_(0,x,d), which equals a_(0,x)^h.

Multiplying by s^-2h cancels each a_(0,d') for d' != x. It leaves
a_(0,x)^(h-1). On root 1 it leaves a_(1) times the product over d of
a_(1,d)^-1. That product is a_(1)^-h, which is a power of a_(1). So
root 1 contributes a_(1)^(1-h), and we get

    c_x = [lambda^(0)_x, s^(2h)] = a_(0,x)^(h-1) a_(1)^(1-h).

`verify_abelian_rank.py` checks this identity table by table for every
tested x, including A_5.

*The generators.* Fix distinct digits x, y, z' and any digit z. This
needs h >= 3, which holds for |A| >= 4. Put

    e_0 = c_x c_y^-1 = a_(0,x)^(h-1) a_(0,y)^(1-h),
    g   = lambda^(0)_(z') lambda^(1)_z,
    e_n = g^n e_0 g^-n.

g has carry 0 and maps the cone (0,w) rigidly onto (0,z',z,w).
Hence e_n = a_(0,(z'z)^n x)^(h-1) a_(0,(z'z)^n y)^(1-h).

*Disjoint supports.* supp e_0 lies in the cones (0,x) and (0,y), and
both are disjoint from (0,z'). For k >= 1,
supp e_k = g^k(supp e_0), which lies in g(cone (0)) = (0,z',z), a
subset of (0,z'). Now take m > n. Then supp e_m = g^n(supp e_(m-n)),
which lies in g^n((0,z')), while supp e_n = g^n(supp e_0). Since g^n
is a bijection, these are disjoint.

*Independence.* Elements with disjoint supports commute. Each e_n acts
on its support as a nonzero power of a localized odometer, so it has
infinite order. A product of powers e_n^(m_n) acts on supp e_n as
e_n^(m_n). So the e_n freely generate Z^infinity inside G, in fact
inside G_e+.

The script checks disjointness and commutation for n <= 3, for A_5,
C_4 and C_5.

**Step 4. The abelian rank bound.** Suppose G = A *_C B is finitely
presented, and A, B are locally virtually abelian. We show that the
abelian subgroups of G have bounded torsion-free rank.

*Setting up the directed system.* Enumerate C, A and B. Let C_n be
generated by the first n elements of C. Let A_n be generated by C_n
and the first n elements of A, and B_n similarly. These are
finitely generated, hence virtually abelian. Put

    G_n = A_n *_(C_n) B_n.

Pushouts commute with directed colimits, so G is the colimit of the
G_n. Write pi_n: G_n -> G for the natural maps.

*Lifting.* Let G = <X | R> be a finite presentation.
- For some n, every x in X has a preimage in G_n.
- Each relator evaluated on these lifts maps to 1 in G. In a directed
  colimit of groups it is therefore already 1 in some G_m.

This gives phi: G -> G_m with pi_m phi = id, so G embeds in G_m.

*The bound in G_m.* Let r be the maximum torsion-free rank of A_m and
B_m. Every vertex stabilizer of the Bass–Serre tree of G_m is a
conjugate of A_m or B_m. Let H <= G_m be abelian.
- If every element of H is elliptic, each finitely generated subgroup
  of H fixes a vertex (Serre, Trees, I.6.5, Corollary 3). So its rank
  is at most r, and hence rank H <= r.
- Otherwise H contains a hyperbolic element t. H commutes with t, so
  it preserves the axis of t. The kernel of the action on the axis
  lies in an edge stabilizer, so it has rank at most r. The image lies
  in D_infinity, so it has rank at most 1. Hence rank H <= r+1.

**Step 5. Conclusions.**
- *R_nu is not finitely presented.* By Steps 1 and 2, G = R_nu
  satisfies the hypotheses of Step 4. By Step 3 it contains Z^infinity,
  whose rank is not bounded.
- *Q and A_1 are not finitely presented.*
  `shell-germ-fp-is-an-ascending-hnn-gate` says that Q finitely
  presented forces R_nu finitely presented, and that this is necessary
  for A_1.
- *Infinite index in B_0.* B_0 is finitely presented by
  `a5-arithmetic-near-group-obeys-parity-charge-constraint`. A
  finite-index subgroup of a finitely presented group is finitely
  presented, so R_nu has infinite index in B_0.

Nothing here addresses finite presentation of E_nu itself.
