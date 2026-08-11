# A computably complete exhaustion of the Leavitt atlas kernel

Date: 2026-08-11

## 1. Purpose

The canonical two-chart atlas in `EXPLICIT_LEAVITT_ATLAS.md` uses

\[
 P=K_1*K_2\cong A_8*A_8
   \mathop{\longrightarrow}^{\rho} Q=L_{\mathbb F_2}(1,2)^\times,
 \qquad R=\ker\rho,
 \qquad N=[P,R].                                      \tag{1}
\]

A fixed finite normal-generating list for `N` exists, but translating a
Krsti\'c--McCool presentation into the two-chart coordinates has not been
done.  That translation is useful for obtaining one fixed optimization, but
it is **not necessary** for a mathematically complete constructive search.

This note gives a nested, computable family of finite constraint sets whose
union normally generates `N`.  It yields a complete sequence of finite
one-unitary optimization problems using exactly the ordinary
`A_8*A_8` source already implemented in `experiments/atlas_two_chart_search.py`.

## 2. A decidable enumeration of the kernel

In each copy of `A_8=GL_4(F_2)`, take the six adjacent elementary
transvections

\[
 e_{12},e_{21},e_{23},e_{32},e_{34},e_{43}.             \tag{2}
\]

They generate `GL_4(F_2)`.  In characteristic two they are involutions.
Let `X` be the resulting symmetric twelve-element generating set of `P`,
six elements in each free factor.

For `L>=1`, let

\[
 W_L=\{w:\ w\text{ is an }X\text{-word of length at most }L,
                 \ \rho(w)=1\},                       \tag{3}
\]

and define the finite constraint set

\[
 \mathcal C_L=\{[x,w]:x\in X,\ w\in W_L\}.             \tag{4}
\]

Identity words may of course be deleted from (4).

**Proposition 1 (effective kernel test).**  The sets `W_L` and
`mathcal C_L` are computable from `L`.

**Proof.**  The set of words of length at most `L` is finite.  The images of
the twelve generators under `rho` are explicit finite leaf matrices in the
binary Leavitt algebra.  Products are computed by multiplying finite sums of
monomials `alpha beta^*`.  Equality is decidable by separating gauge degrees
and refining the right paths in each degree to a common depth.  After that
refinement, equality is equality of two finite matrices over `F_2`.

Equivalently, this is the prefix-refinement normal-form calculation already
used by `atlas_two_chart_search.py` to verify exactly that each of its 54
source words maps to one.  Apply the same calculation to every word in the
finite length window.  This decides membership in (3), after which (4) is
literal word manipulation in the free product.  End proof.

No word-problem oracle for an abstract presentation of `Q` is being assumed:
only the concrete binary-prefix arithmetic of the displayed atlas is used.

## 3. The exhaustion normally generates the exact kernel

**Proposition 2 (commutator exhaustion).**

\[
 N=[P,R]
  =\left\langle\!\left\langle
       \bigcup_{L\ge1}\mathcal C_L
    \right\rangle\!\right\rangle_P .                  \tag{5}
\]

**Proof.**  Every member of every `mathcal C_L` belongs to `[P,R]`, so the
right side of (5) is contained in the left side.  In the quotient by the
right side, every generator `x in X` commutes with every `r in R`, because
`r` is represented by some finite word and hence belongs to some `W_L`.
Since `X` generates `P`, the whole image of `P` centralizes the image of
`R`.  Thus `[P,R]` dies in the quotient, proving the reverse inclusion.
End proof.

There is an unknown but finite stopping window.  Both `P` and
`P/N` are finitely presented, so `N` is finitely normally generated in `P`.
Choose finite normal generators of `N` and express each as a finite product
of conjugates of constraints from the union in (5).  Only finitely many
constraints occur.  Therefore:

**Corollary 3 (existential finite stopping point).**  There is an
`L_0<infinity` such that

\[
 N=\langle\!\langle\mathcal C_{L_0}\rangle\!\rangle_P. \tag{6}
\]

The value of `L_0` is not known, and the exhaustion theorem does not pretend
to compute it.  Its advantage is that one can run a complete increasing
search without knowing it.

## 4. Canonical one-unitary models

Let `lambda:A_8->U(20160)` be the left regular representation.  For
`k>=1` and `U in U(20160k)`, define the exact representation

\[
 \begin{aligned}
  \pi_{k,U}(h)&=\lambda(h)\otimes I_k &&(h\in K_1),\\
  \pi_{k,U}(h)&=U(\lambda(h)\otimes I_k)U^* &&(h\in K_2).
 \end{aligned}                                         \tag{7}
\]

For each finite window put

\[
 \delta_L=
   \inf_{k\ge1}\ \inf_{U\in U(20160k)}
       \max_{c\in\mathcal C_L}\|\pi_{k,U}(c)-1\|_2.  \tag{8}
\]

**Theorem 4 (recursive canonical-atlas criterion).**  The following are
equivalent.

1. `Q=L_(F_2)(1,2)^times` is hyperlinear.
2. `delta_L=0` for every `L>=1`.
3. There are `k_n>=1` and `U_n in U(20160k_n)` such that

   \[
    \max_{c\in\mathcal C_n}
       \|\pi_{k_n,U_n}(c)-1\|_2\longrightarrow0.       \tag{9}
   \]

If these conditions hold, the already proved nonsofic group `Q` is a
hyperlinear nonsofic group.

**Proof.**  Suppose first that `Q` is hyperlinear.  Pull a regular
hyperlinear model of `Q` back to `P`.  Hilbert--Schmidt stability of the
virtually free group `P` corrects it to exact finite-dimensional
representations of `P`.  On either finite factor, the normalized characters
converge to the regular character.  Finite-group character orthogonality,
followed by a harmless common amplification and replacement on an
`o(1)`-dimensional summand, puts both factor restrictions in the canonical
regular form (7).  Every fixed word changes by `o(1)`.  This is the
canonicalization argument from Section 9 of `EXPLICIT_LEAVITT_ATLAS.md`.
It applies to the finite set `mathcal C_L`, for arbitrary `L` and arbitrary
tolerance, and proves `delta_L=0`.  Thus 1 implies 2.

Assume 2.  For every `n`, choose `k_n,U_n` for which the expression in (8),
with `L=n`, is less than `1/n`.  This is (9), so 2 implies 3.

Assume 3 and pass to a tracial ultraproduct.  Since every `pi_(k_n,U_n)` is
an exact representation, (9) defines a homomorphism

\[
 \Pi:P\longrightarrow\prod_\omega U(20160k_n).         \tag{10}
\]

Every member of the union in (5) lies in `ker Pi`; hence `N<=ker Pi`.
The map factors through

\[
 V=P/N.                                                  \tag{11}
\]

This factor is a perfect central extension of `Q`: `R/N` is central by the
definition of `N`, `V/(R/N)=Q`, and `V` is perfect because
`P=A_8*A_8` is perfect.  It is therefore quasisimple.  Indeed, the image in
the simple group `Q` of a normal subgroup of `V` is either trivial or all of
`Q`; in the second case the corresponding quotient of `V` is abelian, hence
trivial because `V` is perfect.

The homomorphism induced by (10) on `V` is nontrivial.  Its restriction to
the first `A_8` factor is the amplified left regular representation at every
stage; any noncommuting pair in that factor has a nonidentity commutator at
normalized distance `sqrt(2)` from one.  Quasisimplicity now puts the kernel
of `V->Pi(V)` in the center.  Thus `Pi(V)` is hyperlinear and `Q` is its
central quotient.  Hyperlinearity passes to central quotients, so `Q` is
hyperlinear.  This proves 3 implies 1.  End proof.

Notice that Theorem 4 does not need the stronger identification of `V` with
the universal central extension, and it does not use finite presentability.
Perfectness plus centrality over the simple quotient is sufficient.

## 5. Smooth finite-window energies

For computation it is convenient to replace the maximum by one smooth
average.  Delete duplicate and identity constraints and put

\[
 E_{L,k}=\min_{U\in U(20160k)}
   \frac1{|\mathcal C_L|}
   \sum_{c\in\mathcal C_L}\|\pi_{k,U}(c)-1\|_2^2,
 \qquad E_L=\inf_{k\ge1}E_{L,k}.                       \tag{12}
\]

Each finite-`k` minimum is attained.  It is the minimum of an explicit
smooth word-trace polynomial on a compact unitary group.  Since a finite
average tends to zero exactly when its finite maximum tends to zero,
Theorem 4 gives

(For a window left empty after deleting identities, set `E_(L,k)=0`.)

\[
 \boxed{Q\text{ is hyperlinear}\quad\Longleftrightarrow\quad
        E_L=0\text{ for every }L.}                     \tag{13}
\]

Block direct sums of relative unitaries show

\[
 (k+\ell)E_{L,k+\ell}
   \le kE_{L,k}+\ell E_{L,\ell}.                       \tag{14}
\]

Hence Fekete's lemma gives

\[
 E_L=\lim_{k\to\infty}E_{L,k}=\inf_k E_{L,k}.         \tag{15}
\]

Combining (6) and (13) produces a finite alternative even though the
stopping window is unknown:

* if `Q` is hyperlinear, every finite-window limiting energy `E_L` is zero;
* if `Q` is nonhyperlinear, some finite computable window has `E_L>0`.

Thus either outcome has a finite-window analytic certificate.  The hard
part remains controlling the limit over multiplicity `k`, not extracting a
printed presentation.

## 6. Relation to the current experiments

The 54 exactly validated source relations in
`experiments/atlas_two_chart_search.py` belong to `R`.  Their 648
commutators with the twelve factor generators therefore belong to the union
in (5).  They are legitimate necessary constraints, but they are not a
complete length window: other kernel words of comparable or smaller word
length were not exhaustively included.

The next complete computational step is now unambiguous:

1. enumerate all `X`-words through a chosen length;
2. retain exactly those whose binary-prefix image is one;
3. form the commutators (4), reduce and deduplicate them; and
4. optimize the energy (12), increasing both `L` and `k`.

Extracting the fixed Krsti\'c--McCool/Tietze relator list would still make a
single fixed-window SOS attack possible.  Theorem 4 shows that it is an
optimization convenience, not a logical prerequisite for a complete
FALSE-side search.
