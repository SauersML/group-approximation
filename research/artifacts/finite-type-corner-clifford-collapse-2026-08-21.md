# Finite-type signed corners are already twisted group algebras

Date: 2026-08-21

## Verdict

The proposed elementary/Steinberg compiler does not create a new
trace-promotion mechanism when its signed projection comes from a
`Gamma`-invariant irreducible representation of a finite normal subgroup.
Clifford theory identifies the entire signed corner as

```text
z_rho C*(Gamma) z_rho  ~=  M_d(C) tensor C*_omega(Gamma/K),       (1)
```

where `d=dim(rho)` and `omega` is a finite-valued scalar cocycle (after a
cohomologous normalization).  Under (1), the normalized canonical corner
trace is

```text
tr_d tensor tau_omega.                                           (2)
```

Consequently, if the corner has unique trace and surjects onto a tracial
C-star algebra whose trace is non-Connes-embeddable, then the twisted group
factor `L_omega(Gamma/K)` is already non-Connes-embeddable.  Passing to the
finite central extension associated to `omega` gives a nonhyperlinear group
without using the BCS algebra.  Thus this finite-normal-sector version of
`character-rigid-signed-bcs-quotient` is exactly a disguised instance of the
existing twisted-factor gate.

There are also two earlier obstructions to using the fixed MIP-star BCS
algebra as the coefficient ring of an elementary group:

1. a quotient of a unique-trace corner is monotracial, whereas the fixed
   source is only known to have traces and to have no CE trace;
2. elementary matrices over a C-star algebra are not unitaries, so the
   canonical coefficient representation does not integrate to a group
   C-star quotient.

## 1. Exact Clifford corner decomposition

Let `K` be a finite normal subgroup of a countable group `Gamma`.  Let
`rho:K -> U(H_rho)` be an irreducible representation of dimension `d` whose
equivalence class is fixed by `Gamma`, and let

```text
q=z_rho=(d/|K|) sum_(k in K) chi_rho(k^-1) k.
```

The invariance assumption says precisely that `q` is central in
`C[Gamma]`.  Put

```text
D=q C[K] q ~= End(H_rho) ~= M_d(C),
Q=Gamma/K.
```

Choose a section `s:Q -> Gamma`.  The homogeneous fibre

```text
A_x=q C[K] s(x) q = D q s(x)
```

is a free rank-one left and right `D`-module.  Conjugation by `q s(x)` is an
automorphism of `D`.  Every automorphism of `M_d(C)` is inner, so choose a
unitary `v_x in D` such that

```text
y_x=v_x q s(x)
```

centralizes `D`.  Normalize `y_e=q`.  Then

```text
y_x y_y y_(xy)^* in A_(xy) A_(xy)^* = D
```

and it centralizes `D`.  Schur's lemma therefore gives a scalar
`omega(x,y) in T` with

```text
y_x y_y=omega(x,y)y_(xy).                                (3)
```

Associativity gives the cocycle identity.  The map

```text
M_d(C) algebraic_tensor C_omega[Q] -> q C[Gamma] q,
a tensor u_x |-> a y_x                                      (4)
```

is a star homomorphism.  It is injective because different fibres have
disjoint `K`-coset support, and it is onto because the fibres exhaust
`qC[Gamma]q`.  Taking universal C-star completions proves (1).

This is the elementary finite-normal-subgroup case of the Mackey/Clifford
obstruction construction.  The only choices change `omega` by a coboundary.
Since `K` is finite, the obstruction class is torsion and may be represented
by a cocycle with values in some finite root group `mu_m`.  One direct way to
see the finiteness is to split `Gamma` first over the kernel of its finite
conjugation image in `Out(K)`: multiplication there contributes only central
elements of the finite group `K`; the remaining quotient is finite, and its
finitely many intertwiner multipliers can be normalized to roots of unity.
Equivalently this is the standard root-of-unity normalization of the
Clifford factor set of a finite-group representation.

## 2. The canonical trace is the twisted regular trace

For `x != e`, every element of `D y_x` is supported on the nonidentity coset
`K s(x)`, hence has canonical group trace zero.  On `D`, the restriction of
the regular trace of `K`, normalized by `tau_Gamma(q)=d^2/|K|`, is the
normalized matrix trace.  Therefore (4) carries

```text
tau_q(a y_x)=delta_(x,e) tr_d(a)                         (5)
```

to `tr_d tensor tau_omega`.  In particular

```text
pi_(tau_q)(q C*(Gamma) q)'' ~= M_d(C) tensor L_omega(Q). (6)
```

Matrix amplification gives an affine bijection between the trace simplexes
of the two C-star algebras in (1).  Thus the signed corner is uniquely
tracial if and only if `C*_omega(Q)` is uniquely tracial.

## 3. Why a non-CE quotient has already solved the problem

Assume the signed corner `A=qC*(Gamma)q` has unique trace and there is a
unital surjection

```text
Phi:A -> B                                                   (7)
```

onto a tracial C-star algebra.  For every trace `sigma` of `B`, uniqueness
gives

```text
sigma Phi=tau_q.                                             (8)
```

Surjectivity identifies the GNS von Neumann algebras, so (6) and (8) give

```text
pi_sigma(B)'' ~= M_d(C) tensor L_omega(Q).                  (9)
```

If `sigma` is non-CE, (9) says that `L_omega(Q)` is non-CE.  Because `omega`
is finite-valued, let

```text
1 -> mu_m -> Qtilde -> Q -> 1
```

be its central extension.  The corresponding central-character corner of
`L(Qtilde)` is `L_omega(Q)`.  A CE `L(Qtilde)` would have all its nonzero
corners CE, contradiction.  Hence `Qtilde` is nonhyperlinear.

The BCS quotient in (7) therefore supplies no bridge that was absent before:
the source signed corner already contains, as its canonical factor, the
non-CE finite-cocycle twisted group factor needed by the existing compiler.

## 4. Elementary matrices do not provide the quotient map

Let `R` be a star subring of a C-star algebra `B`, let `i != j`, and consider
the canonical elementary matrix

```text
E_ij(a)=I+a e_ij in GL_n(B).
```

If it were unitary, then

```text
E_ij(a)^* E_ij(a)
 =I+a e_ij+a^* e_ji+a^*a e_jj=I.                           (10)
```

The `(i,j)` entry of (10) forces `a=0`.  Thus every nontrivial root matrix is
nonunitary.  The canonical map

```text
EL_n(R) -> GL_n(B)
```

is not a unitary representation and cannot integrate to a star homomorphism
from `C*(EL_n(R))` onto `M_n(B)`.  Polar decomposition or Halmos dilation
does not help because neither is multiplicative.  Hyperbolic elementary
unitary groups preserve an indefinite algebraic form; that also does not
make their root transvections unitary for the positive C-star inner product.

An abstract unitary representation of `EL_n(R)` could of course exist, but
then the coefficient-ring map has disappeared.  Asking that such a
representation generate the non-CE GNS factor and simultaneously invoking a
regular-versus-finite-dimensional character theorem already identifies that
factor with the group factor.  This is the desired nonhyperlinearity theorem,
not an elementary-ring construction preceding it.

## 5. Literature scope

The character theorems found in the primary-source audit do not fill this
gap.

- Peterson--Thom, *Character rigidity for special linear groups*,
  arXiv:1303.4007, treats infinite fields and localizations of orders in
  number fields.  Its operator-algebraic superrigidity theorem says that a
  generating factor representation of the relevant arithmetic `PSL` group
  is its regular factor (up to the finite/precompact sector).  Consequently,
  constructing the desired generating non-CE representation for one of
  those groups would already prove the final theorem directly.
- Lavi--Levit, *Characters of the group EL_d(R) for a commutative Noetherian
  ring R*, arXiv:2007.15547 / Adv. Math. 419 (2023), assumes exactly that the
  coefficient ring is commutative and Noetherian.  A BCS star algebra is
  noncommutative, and the theorem does not apply.
- Odd/unitary Steinberg presentations over rings with involution provide
  algebraic central extensions of form-preserving groups, not positive
  Hilbert-space unitary representations of the canonical coefficient
  matrices and not a factorial-character classification over BCS rings.

## 6. Exact frontier consequence

The finite-normal signed-sector proposal has only two possible genuinely new
inputs:

1. first construct a finite-cocycle twisted group factor which is non-CE; or
2. prove a new character theorem for an abstract elementary/unitary group
   together with a generating unitary representation into a non-CE factor.

Input 1 is the existing twisted-factor gate.  Input 2 already proves the
group's regular factor non-CE by the character theorem.  Neither is a weaker
compiler from the current BCS algebra.

