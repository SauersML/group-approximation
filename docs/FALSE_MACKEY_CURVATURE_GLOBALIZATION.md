# Mackey globalization of the local clock curvature

**Closure update for the explicit symmetric double.** No Mackey-globalized
class can satisfy the final central marked/relator separation condition for
this presentation. Its full finite residual \(R\) satisfies \(R=[D,R]\), so
the canonical character ratios are uniformly bounded. The Mackey test below
remains valid for other candidates. See
`FALSE_FINITE_RESIDUAL_COMMUTATOR_NO_GO.md`.

## Why this is the remaining extension problem

The canonical central-quotient criterion separates a character of the finite
relation module into:

1. a pure generator gauge, factoring through
   \(\ker(F_{\rm ab}\to Q_{\rm ab})\); and
2. a curvature character on the Schur multiplier
   \(H_2(Q;\mathbb Z)\).

The pure-gauge sector is uniformly sterile.  The local
Baumslag--Solitar clock supplies a growing projective curvature class on a
finite cyclic/shear subgroup.  The first genuine remaining question is
whether that local class globalizes to the ambient finite quotient without
losing its pairing with the marked cycle.

This question is controlled exactly by the Mackey double-coset operator.

## The exact Mackey test

Let \(H\leq Q\) be finite groups.  Let

\[
\eta\in H^2(H;\mathbb T)
\]

and let

\[
z\in H_2(H;\mathbb Z).
\]

Write

\[
\alpha:=\operatorname{Cor}_H^Q(\eta)in H^2(Q;\mathbb T).
\]

For representatives \(x\in H\backslash Q/H\), put

\[
H_x:=H\cap xHx^{-1}.
\]

The Mackey formula gives

\[
\operatorname{Res}_H^Q\operatorname{Cor}_H^Q(\eta)
=
\sum_{x\in H\backslash Q/H}
\operatorname{Cor}_{H_x}^{H}
\operatorname{Res}_{H_x}^{xHx^{-1}}
(c_x)_*(\eta).
\]

Denote the right-hand side by \(\mathcal M_H^Q(\eta)\).

### Theorem 1 (pairing criterion)

Let \(i:H\hookrightarrow Q\).  Then

\[
\boxed{
\langle\alpha,i_*z\rangle
=
\langle\mathcal M_H^Q(\eta),z\rangle.
}
\]

Consequently, if the right-hand side has order \(p^k\) in \(\mathbb T\),
then the image \(i_*z\in H_2(Q;\mathbb Z)\) has order divisible by \(p^k\),
and the global Schur character \(\alpha\) detects that full order.

#### Proof

Naturality of the homology--cohomology pairing gives

\[
\langle\alpha,i_*z\rangle
=\langle\operatorname{Res}_H^Q\alpha,z\rangle.
\]

Substitute \(\alpha=\operatorname{Cor}_H^Q\eta\) and apply the Mackey
formula.  If the resulting value has order \(p^k\), no element of smaller
order can pair to it, proving the order assertion. \(\square\)

### Corollary 2 (unit-multiple test)

Suppose \(\langle\eta,z\rangle\) has order \(p^k\), and suppose

\[
\langle\mathcal M_H^Q(\eta),z\rangle
=u\langle\eta,z\rangle
\]

for an integer \(u\) with \(p\nmid u\).  Then the transferred global class
\(\alpha\) retains the full \(p^k\)-order marked pairing.

This is the cleanest finite certificate: the total contribution of all
nonidentity double cosets must change the identity-coset contribution only by
a \(p\)-adic unit.

## Stable-elements variant

If \(H\) is a Sylow \(p\)-subgroup of \(Q\), the Cartan--Eilenberg stable
elements theorem gives another exact formulation.  A \(p\)-primary class on
\(H\) globalizes precisely when its restrictions agree under every fusion
map arising from intersections

\[
H\cap xHx^{-1}.
\]

Thus there are two interchangeable finite checks:

- verify the stable-elements equalities on all double-coset intersections;
- or evaluate the Mackey sum and prove the unit-multiple condition above.

Merely proving that the class is nonzero on every intersection is not enough;
the conjugation compatibility and the signed transfer sum must be controlled.

## From global curvature to the presentation character

For finite \(Q\), divisibility of \(\mathbb T\) and the universal coefficient
theorem identify

\[
H^2(Q;\mathbb T)
\cong
\operatorname{Hom}(H_2(Q;\mathbb Z),\mathbb T).
\]

The central relation module lies in

\[
0\to H_2(Q;\mathbb Z)
\to C_Q=L/[F,L]
\to \ker(F_{\rm ab}\to Q_{\rm ab})
\to0.
\]

Hence the global curvature character \(\alpha\) always extends to at least
one character \(\chi:C_Q\to\mathbb T\).  All extensions form an affine
torsor under the pure-gauge character group.  The second and final finite
problem is to choose that gauge so that

\[
\sum_j|\chi([r_j])-1|^2
\]

is negligible compared with

\[
|\chi([w])-1|^2.
\]

This is exactly the paired discriminant--Voronoi repair problem already
isolated elsewhere in the repository.

## Concrete completion certificate

For the \(p^k\)-clock tower, a complete FALSE proof would follow from the
following two finite statements for each \(k\):

1. **Mackey curvature:** the paired local class \(\eta_k\) and marked cycle
   \(z_k\) satisfy
   \[
   \langle\mathcal M_{H_k}^{Q_k}(\eta_k),z_k\rangle
   =u_k\langle\eta_k,z_k\rangle,
   \qquad p\nmid u_k,
   \]
   so the full \(p^k\)-order class globalizes to \(Q_k\).
2. **Gauge repair:** some extension \(\chi_k:C_{Q_k}\to\mathbb T\) of that
   global class satisfies
   \[
   \frac{\sum_j|\chi_k([r_j])-1|^2}
   {|\chi_k([w])-1|^2}\longrightarrow0.
   \]

Character powering and the projective-regular construction then produce the
required tracial ultraproduct representation and a hyperlinear nonsofic
image.

This formulation replaces simultaneous matrix covariance by finite group
homology, finite double-coset arithmetic, and a finite abelian gauge problem.
