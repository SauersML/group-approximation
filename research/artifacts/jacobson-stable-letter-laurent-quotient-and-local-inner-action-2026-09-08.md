# The stable-letter Laurent quotient and its locally inner core action

2026-09-08. The literal bilateral image of `Theta_shift`, modulo its
finitary subgroup, is exactly
`SL_3(F_2[z,z^(-1)]) x Z`. The kernel of the literal action is
canonically the kernel of the specified Laurent homomorphism from
the abstract quotient group `Lambda`. It centralizes the stable
letter. These statements do not identify `Lambda` itself with the
Laurent matrix group, and do not prove a uniform matrix gap.

Separately, every conjugation action on a finite core packet is
implemented by a finitary element. A finite collection of such
covariance equations has an exact regular matrix model. This does
not force the implementing actor words to satisfy their multiplication
relations.

Use the finite presentation and literal action from
[the stable-letter construction](jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md),
the normal finitary subgroup and quotient presentation from
[the finite-packet reconstruction](jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md),
and the positive-tail symbol construction from
[the amenable-target obstruction](jacobson-recursive-head-dies-in-amenable-targets-2026-09-08.md).
Write

```text
Gamma=Theta_shift,
pi:Gamma->GL(V_Z),
V_Z=directSum_(n in Z) F_2^3,
H=<G_Q,G_P,h>,
L=normalClosure_Gamma(w),       w=x_13,Q,
R=F_2[z,z^(-1)].
```

The established restriction of `pi` to `L` is a faithful
identification with all finitary invertible matrices on the bilateral
basis. Also

```text
Gamma/L ~= Lambda x Z,                                  (1)
```

with the explicit two-finite-factor presentation of `Lambda` in
Section 7 of the finite-packet artifact. The image of `t` in (1)
is the generator of the second factor.

## 1. The complete positive-tail symbol image

Every literal generator and its inverse has finite propagation in
the level coordinate and is eventually translation invariant on the
positive tail. The same is true of every product. Consequently, for
each `A in pi(Gamma)`, there are unique finitely many coefficient
matrices `A_k in M_3(F_2)` such that, for all sufficiently large `n`,

```text
A e_(j,n)=sum_(i,k) (A_k)_(ij) e_(i,n+k).
```

Uniqueness follows from independence of the displayed basis vectors.
Define `sigma(A)=sum_k A_k z^k`. Composing operators on a
sufficiently remote positive tail multiplies these Laurent matrices.
Applying this to inverse operators proves that

```text
sigma:pi(Gamma)->GL_3(R)                                (2)
```

is well defined on the literal operator group. In particular, the
definition does not depend on choosing a word for an operator.

The symbols of the generators are

```text
sigma(pi(g_Q))=I,          sigma(pi(g_P))=g,

sigma(pi(h))=[[0,z,0],
              [z^(-1),0,0],
              [0,0,1]],

sigma(pi(t))=z I_3.                                    (3)
```

The symbols of the generators of `H` all have determinant one.
Its symbol image contains the constant `SL_3(F_2)` and

```text
d=sigma(pi(h w_12,P))=diag(z,z^(-1),1).
```

For every integer `n`, it therefore contains

```text
d^n x_13(1) d^(-n)=x_13(z^n).
```

Conjugating by constant coordinate permutations supplies every
`x_ij(z^n)`, `i!=j`. Root addition
`x_ij(f)x_ij(g)=x_ij(f+g)` then supplies every `x_ij(f)` for
`f in R`.

For completeness, these elementary matrices generate `SL_3(R)`.
The ring `R` is Euclidean: for nonzero `f`, use

```text
nu(f)=largest exponent of f minus smallest exponent of f.
```

Multiplication by a Laurent unit normalizes a nonzero Laurent
polynomial to a polynomial with nonzero constant term. Polynomial
division after these normalizations gives a remainder whose `nu`
is strictly smaller than that of the divisor. Euclidean elementary
row operations therefore reduce a unimodular column to one unit
entry and zeros. The necessary unit rescaling is elementary as well.
For a unit `u in R`, in a two-coordinate block and characteristic two,

```text
w(u)=x_12(u)x_21(u^(-1))x_12(u)
    =[[0,u],[u^(-1),0]],

w(u)w(1)=diag(u,u^(-1)).
```

Thus elementary row and column reduction of a determinant-one
matrix reduces it to the identity, including its remaining
two-coordinate determinant-one block. Hence

```text
sigma(pi(H))=SL_3(R).                                  (4)
```

The stable letter adds the central Laurent scalar `z I_3`.
Its cyclic subgroup meets `SL_3(R)` trivially, since
`det(z^k I_3)=z^(3k)`. Therefore the full image of (2) is

```text
sigma(pi(Gamma))
 =SL_3(R) . <z I_3>
 ~=SL_3(R) x Z,                                        (5)
```

where the displayed isomorphism sends `(M,k)` to `M z^k I_3`.

The elementary Laurent image and the unilateral finitary symbol
kernel already occur in the
[earlier ring-symbol calculation](../binary-jacobson-rank-two-dichotomy-proof.md).
The argument here verifies the literal image of this separately
specified stable-letter presentation directly from its generators.

## 2. Its symbol kernel is exactly the bilateral finitary subgroup

Let `A=pi(g)` have identity positive-tail symbol. If `k` is
the total exponent of `t` in `g`, (3) gives

```text
det(sigma(A))=z^(3k).
```

Thus `k=0`. Far enough along the negative tail the original
generators `g_Q,g_P,h` act identically, whereas `t` translates
the level by one. For any fixed word, taking the input sufficiently
negative ensures that every intermediate level stays in this
identity region. Its eventual negative action is therefore
translation by `k`, and is the identity when `k=0`.

Identity positive symbol also says that `A` fixes every basis
vector sufficiently far along the positive tail. Only finitely many
basis vectors remain. Their images have finite support, so `A-I`
has only finitely many nonzero matrix entries. Enlarging the finite
coordinate set to contain the affected columns and rows expresses
`A` as an invertible finite block plus the identity. It therefore
belongs to `pi(L)` by the proved description of that subgroup.
Conversely every element of `pi(L)` has identity symbol. Hence

```text
ker(sigma)=pi(L),
pi(Gamma)/pi(L) ~= SL_3(R) x Z.                         (6)
```

This proves exactness for the literal group. It does not assert
that `pi` is faithful on all of `Gamma`.

## 3. The abstract literal kernel is the Laurent-cover kernel

Let

```text
q:Gamma->Gamma/L ~= Lambda x Z.
```

Since (2) kills `pi(L)`, the positive symbol of the literal action
factors through `q`. Under the product identification in (5),
the induced map is

```text
Lambda x Z -> SL_3(R) x Z,
(lambda,k) |-> (kappa(lambda),k),                       (7)
```

where `kappa` sends the original tail factor of `Lambda` to the
constant `SL_3(F_2)` and sends its generator `h` to the Laurent
matrix in (3). The group `Lambda` has exactly the quotient
presentation stated in (1); (7) makes no additional identification
of that abstract group. Equation (4) proves that `kappa` is
surjective.

The restriction of `q` gives a canonical group isomorphism

```text
ker(pi) ~= ker(kappa) x {0}.                            (8)
```

First it is injective, since `ker(pi) intersect L={1}` by
faithfulness on the finitary subgroup. For surjectivity, take any
element of `ker(kappa) x {0}` and lift it to `x in Gamma`.
Its positive symbol is trivial, so (6) gives `pi(x) in pi(L)`.
Choose `ell in L` with `pi(ell)=pi(x)`. The element
`x ell^(-1)` lies in `ker(pi)` and has the required image under
`q`. This proves both directions of (8).

There is also an exact centralization relation:

```text
[ker(pi),t]=1.                                         (9)
```

Indeed for `x in ker(pi)`, the commutator `[x,t]` lies in
`ker(pi)` by normality. It lies in `L` as well, because `q(t)`
is central in `Lambda x Z`. Their intersection is trivial, proving
(9).

Together with the previously established
`C_Gamma(L)=ker(pi)`, this locates the remaining ambiguity
precisely: the literal kernel centralizes `L` and `t`, and is
isomorphic to the kernel of the specific surjection `kappa` in
(7). The subsequent
[affine quotient proof](jacobson-laurent-cover-has-a-noncentral-affine-quotient-2026-09-08.md)
shows that `ker(kappa)` maps onto the infinite natural module
`R^3` and is noncentral. Consequently `kappa` is not injective,
and `ker(pi)` is infinite and noncentral in the whole group
`Gamma`. None of (6)--(9) gives a positive lower bound for
the unrestricted matrix-gap problem.

## 4. The action on each finite core packet is exactly inner

Let `X=Z x {1,2,3}`, let `V_E` denote the span of a finite
coordinate set `E` in `X`, and let `V_(E^c)` be its coordinate
complement. Fix `g in Gamma` and put `A=pi(g)`. Every literal
generator and its inverse has finite propagation, hence so do
`A,A^(-1)`. In particular the coordinate functionals
`epsilon_j A^(-1)`, for `j in E`, have finite support.

Choose a finite coordinate set `D` containing `E`, all coordinate
supports of `A(V_E)`, and all supports of these inverse-row
functionals. Set

```text
W_D={x in V_D : epsilon_j A^(-1)x=0 for all j in E}.
```

The functionals are the inverse-coordinate dual basis on `A(V_E)`,
so

```text
V_D=A(V_E) directSum W_D.
```

Choose a linear isomorphism `v:V_D->V_D` which equals `A` on
`V_E` and maps `V_D intersect V_(E^c)` isomorphically onto
`W_D`. Extend `v` by the identity on `V_(D^c)`. The inverse-row
support condition then gives, globally,

```text
v e_j=A e_j,
epsilon_j v^(-1)=epsilon_j A^(-1)          (j in E).
```

Indeed the functionals agree on `A(V_E)` and vanish on both
`W_D` and `V_(D^c)`. Therefore

```text
v (I+e_i epsilon_j) v^(-1)
 =A (I+e_i epsilon_j) A^(-1)              (i,j in E, i!=j).
```

The elementary roots generate `GL(E)`, proving equality of the
two conjugation actions on the whole packet. The finitary map `v`
corresponds to an element of `L`. Both abstract conjugates lie in
normal `L`; faithfulness of `pi|L` upgrades the literal calculation
to

```text
v f v^(-1)=g f g^(-1)                    (f in GL(E)).    (10)
```

One common `E` may contain any prescribed finite family of core
packets. The same `v` then works on every packet and on all their
intersections; no independent identifications are being chosen.

## 5. Finite covariance diagrams have exact matrix models

Let `S` be a finite list of actor generators, let `F<=L` be a
finite subgroup, and choose finitely many words in `S union S^(-1)`
whose conjugation actions on `F` are to be inspected. Let `D_0`
be the finite union of `F` and all intermediate conjugates of its
elements encountered while evaluating those words from right to left.
All these elements belong to `L` by normality. Enlarge a finite
coordinate set `E` to support every element of

```text
D_0 union union_(s in S) s^(-1) D_0 s.
```

For each `s in S`, Section 4 supplies one `v_s in L`
implementing `Ad_s` on `GL(E)`. Use `v_s^(-1)` for the inverse
letter. The additional inverse-conjugate supports ensure that
`v_s^(-1)` implements `Ad_(s^(-1))` on `D_0` as well.
Explicitly, for `x in D_0`, the element `s^(-1)x s` belongs
to `GL(E)`, and applying (10) to that element gives

```text
v_s (s^(-1)x s) v_s^(-1)=x,
v_s^(-1)x v_s=s^(-1)x s.
```

Consequently every selected actor word has exactly its prescribed
conjugation action on `F` when its letters are replaced by the
corresponding `v_s` or `v_s^(-1)`.

All inspected core elements and all `v_s` lie in one larger finite
packet `Q=GL(D')`. Its regular complex representation gives an
exact finite-dimensional unitary model of this entire finite
covariance diagram. It is faithful on the full complex group algebra
of every inspected core subgroup: its restriction to such a subgroup
is a direct sum of regular representations. Thus this realizes full
operator norms and multiplication on the inspected core, not merely
dimensions or character values.

If a selected actor word is an identity in `Gamma`, its implementer
word centralizes `F`. It need not be the identity in `Q`. That
distinction is the unsolved coherence requirement: the construction
imposes conjugation identities, but does not automatically impose
the actors' mixed multiplication relations. Nor does it assert that
every previously fixed representation of a smaller core packet
extends to the chosen larger packet. The result limits arguments
based only on finite-core covariance; it does not rule out
representation-theoretic methods that use the remaining relations.
