# Profinite-synchronized HNN extensions are regularly MF

This note proves the permanence theorem recorded in
`profinite-synchronized-hnn-is-regular-mf` and derives the exact finite
quotient condition needed by the Higman rope.  It does **not** assert that the
rope presently satisfies that condition.

## 1. Finite regular representations synchronize the edge

Let `theta_0,theta_1:S->A` be injective, and let `p_n:A->A_n` be finite
quotients satisfying `(PSH1)--(PSH2)`.  Replace the sequence by cumulative
products if necessary; this preserves `(PSH2)` and makes every nonidentity
element survive eventually.

Put

```text
rho_n=lambda_(A_n) o p_n : A -> U(l2(A_n)).             (1)
```

For `i=0,1`, let `S_(i,n)=p_n(theta_i(S))`.  The edge map induces an
isomorphism

```text
S_(0,n) -> S_(1,n),
p_n(theta_0(s)) |-> p_n(theta_1(s)),                    (2)
```

because the two maps have the same kernel.  Restricting `lambda_(A_n)` to a
subgroup `K` gives `[A_n:K]` copies of `lambda_K`.  The two groups in `(2)`
have the same order, so there is a unitary `u_n` with

```text
u_n rho_n(theta_0(s)) u_n^*=rho_n(theta_1(s))           (3)
```

for every `s`.

Let `Q_M` be the norm matrix corona containing the classes of the sequences
`rho_n(a)`, after harmless repetition to use one matrix-size sequence, and put

```text
rho(a)=[rho_n(a)],            D=C*(rho(A)) <= Q_M.       (4)
```

Eventual separation makes `rho` injective.  The algebra `D` is separable and
MF because it is a C-star subalgebra of a norm matrix corona.  Equation `(3)`
gives a unitary `u=[u_n]` and a C-star isomorphism

```text
alpha=Ad(u): B_0 -> B_1,
B_i=C*(rho(theta_i(S))) <= D.                            (5)
```

## 2. The universal C-star HNN algebra is MF

Write `B=B_0` and identify `B_1` with `B` by `alpha`.  Ueda's universal-HNN
corner theorem identifies

```text
HNN(D,B,alpha)
  ~= e_11 [ M_2(D) *_(B directSum B) M_2(B) ] e_11,     (6)
```

where `B directSum B` enters `M_2(D)` as

```text
(b_0,b_1) |-> diag(b_0,alpha(b_1))                     (7)
```

and enters `M_2(B)` diagonally in the standard two corners.

The inclusion `D<=Q_M` embeds `M_2(D)` into `M_2(Q_M)`.  Embed `M_2(B)` into
the same corona by

```text
x |-> diag(1,u) x diag(1,u)^*.                          (8)
```

On the common diagonal algebra, `(8)` is exactly `(7)`.  Shulman's Theorem
20 therefore makes the amalgam in `(6)` MF.  MF passes to C-star subalgebras,
so its full corner, the universal HNN algebra, is MF.

The two external inputs are precisely:

- Yoshimichi Ueda, *A relationship between HNN extensions and amalgamated
  free products in operator algebras*, the universal-HNN full-corner
  identification;
- Tatiana Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564v2, Theorem 20, the compatible matrix-corona criterion.

## 3. The abstract group embeds and the trace is regular

Fix a free ultrafilter and let

```text
tr(rho(a))=lim_U tr_(A_n)(rho_n(a)).                    (9)
```

This is the regular character of `A`: it is `1` at the identity and `0` at
every other group element by eventual separation.  Coordinatewise unitary
conjugacy in `(3)` shows that `alpha` preserves the edge trace.

In the GNS finite von Neumann algebra of `(D,tr)`, take the trace-preserving
conditional expectations onto the two edge von Neumann algebras and form the
reduced von Neumann HNN extension.  For `a` outside the relevant edge
subgroup, regularity gives

```text
E_i(rho(a))=0:                                          (10)
```

indeed `rho(a)` is orthogonal to every `rho(theta_i(s))` in `L^2(tr)`.
The reduced-HNN moment formula and `(10)` say that every nonidentity
Britton-reduced group word has trace zero.  Hence the canonical map

```text
<A,t | t theta_0(s)t^-1=theta_1(s)> -> U(HNN(D,B,alpha))
```

is injective, and the pulled-back trace is the regular character.  Since the
target C-star algebra is MF, this is a regular operator-MF realization.

## 4. Specialization to the Higman graph edge

For

```text
A=Gamma times Q,
theta_0(s)=(s,1),             theta_1(s)=(s,tau(s)),
p_n=(alpha_n,beta_n),
```

the two kernels are

```text
ker(p_n theta_0)=ker(alpha_n|S),
ker(p_n theta_1)=ker(alpha_n|S) intersect ker(beta_n tau).
```

Thus `(PSH2)` is equivalent to

```text
ker(alpha_n|S) <= ker(beta_n tau).                     (11)
```

This calculation is why independent residual finiteness of `Gamma` and `Q`
does not close the compiler: their finite quotients must be synchronized by
`(11)`.  A congruence-extension construction for the inclusion
`S<=Gamma`, compatible with `tau`, would supply it.  Establishing that
construction uniformly is the remaining claim
`positive-rope-profinite-edge-synchronization`.

## 5. Why the tempting general lifting shortcut is not used

Shulman's lifting characterization does not by itself show that every HNN
extension of a group with MF full C-star algebra is group MF.  Lifting the
base representation leaves an operator-norm intertwiner problem for the
stable unitary.  The standard two-by-two unitary-lifting trick pairs an
intertwiner with its adjoint; for an asymmetric HNN edge the adjoint has the
reverse orientation and is not a second representation of the same HNN
extension unless an additional edge-swapping symmetry exists.

The proof above avoids that gap: the conjugating unitaries already exist in
each finite quotient, so the required compatibility is exact in the norm
matrix corona before Ueda's corner theorem is applied.
