# Full-group density does not produce a nonhyperlinear discrete group

Date: 2026-08-13

## 1. The exact group-factor certificate

Let \(\mathcal R\) be an aperiodic ergodic pmp equivalence relation on
\((X,\mu)\), let \(M=L(\mathcal R)\), and let \([\mathcal R]\) be its
measured full group.  Write \(u_T\in M\) for the canonical unitary of
\(T\in[\mathcal R]\).  If a countable subgroup
\(\Lambda\leq[\mathcal R]\) has both properties

\[
 \mu(\operatorname{Fix}(g))=0\quad(1\ne g\in\Lambda),             \tag{FDG1}
\]

and

\[
 W^*(u_g:g\in\Lambda)=M,                                         \tag{FDG2}
\]

then the canonical map extends to a trace-preserving isomorphism

\[
 L(\Lambda)\cong M.                                               \tag{FDG3}
\]

Indeed, the groupoid trace satisfies

\[
 \tau_M(u_g)=\mu(\operatorname{Fix}(g))=\delta_{g,1}.             \tag{FDG4}
\]

Thus the representation of \(\mathbf C[\Lambda]\) in \(M\) has the
regular trace.  Its GNS completion is \(L(\Lambda)\), faithfulness follows
from the faithful regular trace, and `(FDG2)` gives surjectivity.

Consequently, if \(M\) is not Connes embeddable, any countable subgroup
satisfying `(FDG1)--(FDG2)` is nonhyperlinear.  This is a valid and very
short conversion of Manzoor-type non-CE equivalence relations into the
discrete-group problem.  Its missing hypothesis is exactly a **group-factor
realization**, not merely finite generation of the measured full group.

There is in fact a stronger obstruction: on a nontrivial probability
space, `(FDG1)` and `(FDG2)` can never hold simultaneously.  Let

\[
 E_A:L(\mathcal R)\longrightarrow A=L^\infty(X)
 \tag{FDG4a}
\]

be the canonical conditional expectation.  Essential freeness gives

\[
 E_A(u_g)=0\quad(1\ne g\in\Lambda),
 \qquad E_A(u_1)=1.                                    \tag{FDG4b}
\]

It follows first on the group algebra, and then by normality of `E_A`, that

\[
 E_A\bigl(W^*(u_g:g\in\Lambda)\bigr)=\mathbf C1.       \tag{FDG4c}
\]

If `(FDG2)` held, then every `a in A` would belong to the algebra on the
left.  But `E_A(a)=a`, so `(FDG4c)` would force `A=C1`, contrary to the
aperiodic nontrivial hypothesis.  Therefore

\[
 \boxed{
 \Lambda\le[\mathcal R]\text{ essentially free}
 \quad\Longrightarrow\quad
 W^*(u_g:g\in\Lambda)\ne L(\mathcal R).
 }
 \tag{FDG4d}
\]

Thus the sufficient certificate `(FDG1)--(FDG2)` is logically correct but
vacuous for every nontrivial pmp equivalence relation.  The obstruction is
not merely topological density: the regular-trace subgroup algebra has
scalar Cartan expectation, whereas the relation algebra contains its whole
diffuse Cartan.

## 2. Why uniform density cannot supply even an approximation to the certificate

Equip \([\mathcal R]\) with the uniform metric

\[
 d_u(S,T)=\mu(\{x:Sx\ne Tx\}).                                   \tag{FDG5}
\]

Call a subgroup essentially free if it satisfies `(FDG1)`.  Let
\(T\in[\mathcal R]\) be nonidentity and suppose its support is not conull.
For every nonidentity element \(g\) of an essentially free subgroup,

\[
 \operatorname{Fix}(T)\setminus\operatorname{Fix}(g)
 \subseteq\{x:gx\ne Tx\}.
\]

Since \(\mu(\operatorname{Fix}(g))=0\), this gives

\[
 d_u(g,T)\geq\mu(\operatorname{Fix}(T))>0.                        \tag{FDG6}
\]

The identity is at distance \(\mu(\operatorname{supp}T)>0\) from \(T\).
Hence \(T\) is not in the uniform closure of the subgroup.

Every aperiodic full group contains nonidentity elements of arbitrarily
small positive support: restrict a nontrivial involution to a small
measurable subset on which it swaps two equimeasurable pieces.  Therefore:

**Theorem (density/freeness incompatibility).**  No essentially free
subgroup of the measured full group of a nontrivial aperiodic pmp
equivalence relation is dense in the uniform topology.

This excludes the proposed shortcut

\[
 \text{topologically finitely generated full group}
 \;\Longrightarrow\;
 \text{finitely generated regular-trace generator of }L(\mathcal R).
                                                                    \tag{FDG7}
\]

Topological finite-generation theorems produce dense subgroups whose
nonidentity elements necessarily have positive-measure fixed sets.  Their
canonical groupoid characters are therefore not the regular character.

## 3. Full-group unitaries themselves do generate the relation algebra

The obstruction in Section 2 is not caused by a failure of the whole full
group to see the Cartan algebra.  In fact

\[
 W^*(u_T:T\in[\mathcal R])=L(\mathcal R).                         \tag{FDG8}
\]

Here is a direct proof of the only nonformal inclusion.  Given a measurable
set \(A\), aperiodicity supplies an element \(T_A\in[\mathcal R]\) which is
the identity on \(X\setminus A\) and whose orbits in \(A\) are infinite.
In the standard groupoid representation, the spectral projection of
\(u_{T_A}\) at the eigenvalue \(1\) is exactly \(1_{X\setminus A}\): on
the complement the unitary is the identity, while on an infinite orbit it
is a bilateral/permutation shift with no \(\ell^2\) fixed vector.  Borel
functional calculus therefore puts \(1_A\) in the von Neumann algebra
generated by full-group unitaries.  Hence it contains
\(L^\infty(X)\); together with all full-group normalizers this generates
\(L(\mathcal R)\).

Uniform density would therefore imply `(FDG2)`, but `(FDG4d)` proves that it
can never coexist with `(FDG1)` for any reason, not only because uniform
density is too strong.  A successful conversion cannot use the canonical
full-group unitaries of an essentially free subgroup to generate the
relation algebra.  It needs a genuinely different group-factor realization
or a trace-preserving embedding of the non-CE algebra into a group factor.

## 4. Consequence for the current literature

The 2026 classification of finite-factor characters for topological full
groups of Cantor minimal \(\mathbb Z\)-systems concerns amenable orbit
relations and does not provide `(FDG1)--(FDG2)` for a non-CE relation.
Likewise, topological-rank and dense-generation results for measured full
groups cannot be combined with Manzoor's example through `(FDG7)`.

The previously stated bridge through an essentially free W*-generating full
subgroup is closed by `(FDG4d)`.  The exact remaining bridge is stronger:
construct a discrete group factor which contains the non-CE relation algebra
trace-preservingly (or realize it as a corner) by operators other than the
canonical implementing unitaries alone.  Uniform density, free stabilization,
and character classification do not supply such an embedding.
