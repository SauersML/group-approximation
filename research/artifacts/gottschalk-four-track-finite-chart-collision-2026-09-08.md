# Exact finite-chart collision for cyclic bilinear feedback

Date: 2026-09-08. This disproves injectivity of one explicit encoder;
it does not prove surjunctivity of the Leavitt unit group.

Work over the binary Leavitt algebra, with

    t_i s_j = delta_ij,       s_0 t_0 + s_1 t_1 = 1.

The two embedded GL_4(F_2) chart groups have ordered leaves

    D_1 = (01, 1, 000, 001),
    D_2 = (00, 1, 010, 011).

Write K_1 for the first chart group. In either chart use the matrices

    a = [0 1 1 0]             b = [1 0 0 0]
        [1 1 1 0]                 [0 1 0 0]
        [0 0 1 0]                 [0 1 1 1]
        [0 0 0 1]                 [0 0 1 0].

Their copies are a_1,b_1 in the first chart and a_2,b_2 in the second.
These are the four atlas generators from
`experiments/atlas_four_generator_certificate.py`.

## Independent separation of the two charts

The inverse of a is

    a^-1 = [1 1 0 0]
           [1 0 1 0]
           [0 0 1 0]
           [0 0 0 1].

Column 2, indexed from zero, of a^-1 b is (0,1,1,1)^T. Consequently

    (a_2^-1 b_2) s_010 = s_1 + s_010 + s_011,
    t_1 (a_2^-1 b_2) s_010 = 1.

For any h in K_1, expand h s_01 in the first chart and use
s_010=s_01 s_0. All its leaves except 1 are killed by t_1, so

    t_1 h s_010 = h_(1,01) s_0,       h_(1,01) in F_2.

This is either 0 or s_0, never 1. Indeed t_1 is nonzero because
t_1 s_1=1, whereas t_1 s_0=0. Thus

    a_2^-1 b_2 is not in K_1.

This is an exact algebraic separation, independent of a finite
enumeration or an approximation of the group.

## The collision

For binary configurations define

    B(U,V)(g) = U(g a_1)V(g b_1) + U(g a_2)V(g b_2).

Let Z=1_(K_1). Since a_1,b_1 belong to K_1, the first summand in
B(Z,Z)(g) equals Z(g). The second summand is always zero: simultaneous
membership of g a_2 and g b_2 in K_1 would put
(g a_2)^-1(g b_2)=a_2^-1 b_2 in K_1. Therefore

    B(Z,Z)=Z.

For any cyclic number m>=3 of tracks, set

    F_i(X)=X_i+B(X_(i+1),X_(i+2)),       indices modulo m.

Then

    F(Z,...,Z)=0=F(0,...,0).

In particular the proposed four-track encoder is not injective. Its
nonzero colliding input has finite support: K_1 has order 20160, so
the four-track input has 80640 occupied track-sites. All constant
configurations are fixed by F, which shows why tests confined to
constant backgrounds missed this collision.

## Reusable exact design test

For any group and

    B(U,V)(g)=U(ga)V(gb)+U(gc)V(gd),

if a subgroup H contains a,b but excludes c^-1 d, then
B(1_H,1_H)=1_H. Finiteness of H is unnecessary for the collision;
it only makes its support finite. The same argument applies after
interchanging the two summands.

Thus using two different finite charts, or making all memory actors
generate the whole group, does not protect a cyclic encoder from a
monochromatic subgroup mask. Any replacement must invalidate this
specific fixed-mask identity, as well as produce a literal local
left inverse and a nonzero reverse-composition defect. This artifact
supplies neither of those latter ingredients for a replacement.
