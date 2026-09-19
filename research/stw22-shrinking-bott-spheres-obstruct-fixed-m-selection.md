---
rg: 2
id: stw22-shrinking-bott-spheres-obstruct-fixed-m-selection
kind: route
title: Scale the first Stiefel sphere into arbitrarily small half-slack weighted balls
target: stw22-fixed-replication-blocks-infinite-dimensional-selection
requires:
  - stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
  - stw22-matrix-weighted-copy-uniform-finite-degree-fillings
artifacts:
  - research/artifacts/stw22-infinite-dimensional-selection-barrier-audit-2026-08-31.md
---

Fix m>=1, put n=2m, and equip M_n with normalized trace.  Let

    p=e_1 e_1^*,       a_lambda=lambda p,       0<lambda<=1.

The support condition is exactly half slack:

    m tau(p)=m/(2m)=1/2.                                (SB-1)

The polar-frame identification sends the fibre to V_m(C^(2m)).  It is
useful to write the first obstruction before invoking that identification.
Let

    B=span{e_1,e_(m+1),...,e_(2m)} ~= C^(m+1).

For x in the unit sphere S(B)=S^(2m+1), define the m-tuple

    v_1(x)=sqrt(lambda) x e_1^*,
    v_i(x)=sqrt(lambda) e_i e_1^*       (2<=i<=m).       (SB-2)

The vectors x,e_2,...,e_m are orthonormal.  Hence

    v_i(x)^*v_j(x)=delta_(ij) a_lambda,

and their range positives are pairwise orthogonal, so (SB-2) lies in the
weighted-copy fibre.  Under polar decomposition it is the frame

    (x,e_2,...,e_m) in V_m(C^(2m)).                     (SB-3)

Forget the first vector.  The resulting fibration is

    S^(2m+1) -> V_m(C^(2m)) -> V_(m-1)(C^(2m)).         (SB-4)

The base has codimension m+1 and is (2m+2)-connected.  Its long exact
homotopy sequence therefore makes the fibre inclusion an isomorphism on
pi_(2m+1).  Thus (SB-2) represents a generator of

    pi_(2m+1)(V_m(C^(2m)))=Z.                           (SB-5)

At the base point x=e_1, the normalized Hilbert-sum metric gives the exact
formula

    d_2(v(x),v(e_1))
      =sqrt(lambda/(2m)) ||x-e_1||
      <=2 sqrt(lambda)/sqrt(2m).                        (SB-6)

For any proposed positive local filling radius, choose lambda so small
that the right side of (SB-6) is below it.  The resulting sphere is
contained in that ball but cannot extend over B^(2m+2), even without a
radius restriction, by (SB-5).  This proves failure of
equi-LC^(2m+1) for the fixed-m half-slack family.

The same construction in n=2m+1 has complement rank m+1 and satisfies

    m tau(p)=m/(2m+1)<1/2.

Now vary x in the sphere of

    span{e_1,e_(m+1),...,e_(2m+1)} ~= C^(m+2).

The forgetful fibration identifies it with the generator in degree
2m+3, and its radius is at most 2sqrt(lambda/(2m+1)).  Hence the barrier
is not an artefact of equality in (SB-1).

For completeness, every nonzero half-slack matrix fibre has k>0 and c>0.
The unitary fibration shows that V_k(C^n) is 2c-connected and its first
nonzero group is pi_(2c+1)=Z.  Thus each such finite Stiefel value already
fails global C-infinity.

There is one tempting but invalid shortcut.  If rank(p)=d, then k=md and
n=k+c; half slack is equivalent to

    md<=c.                                               (SB-7)

Fixed m and fixed c therefore bound d and n.  One cannot keep c fixed and
send n to infinity inside the half-slack family.  The projection sequence

    n=2md,       k=c=md,       d->infinity

does give shrinking essential spheres, but their dimensions 2md+1 also
grow.  It rules out a single modulus uniform in the homotopy degree, not
the usual degreewise equi-LC^j property.  The scaled-weight construction
(SB-1)--(SB-6) is what gives a valid fixed-degree obstruction.

An infinite-dimensional Michael continuation based on one fixed m would
need its values to meet connectivity and local-connectivity hypotheses in
all degrees.  Equations (SB-5)--(SB-6) show that these exact matrix values
do not.  The finite-dimensional proof avoids the obstruction by fixing D,
choosing m>=ceil((D-1)/2), and stopping below the first Stiefel group.
No conclusion about the truth of the root infinite-dimensional trace
problem follows.
