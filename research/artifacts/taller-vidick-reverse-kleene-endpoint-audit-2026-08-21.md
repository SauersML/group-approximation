# Taller--Vidick at epsilon zero: reverse-Kleene endpoint audit

Primary source: Aviv Taller and Thomas Vidick, *Approximating the quantum
value of an LCS game is RE-hard*, arXiv:2507.22444v2 (2026), especially
Definition 4.1, Proposition 4.1, Lemma 4.2, and Theorem 5.2 in the v2 TeX
numbering.  The abstract explicitly says that the `epsilon=0` endpoint would
imply a nonhyperlinear group.

## 1. The exact implication from near-perfect play to `J`

For a fixed finite LCS `L`, let `Gamma_L` be its solution group and `J` the
central involution.  There are two different statements:

```text
omega_q(L)=1                         => J!=1,             (A)
one strategy has value >=1-epsilon  => J!=1.             (B)
```

Statement `(A)` follows from the standard approximate-representation
correspondence: if `J=1`, choose a finite normal-closure derivation `D` of
`J`.  A strategy of loss `eta` gives an approximate solution-group tuple with
relator errors `O_L(sqrt eta)`.  Telescoping along the finitely many relator
uses in `D` forces its image of `J` close to `I`, while the LCS construction
places it at `-I`.  Thus

```text
eta >= gamma(L,D)>0.                                      (1)
```

All constants in (1) are computable from the finite game and the displayed
derivation.  No uniform lower bound in `L,D` follows.  Consequently `(B)` is
valid only under the additional numerical hypothesis

```text
epsilon < gamma(L,D).                                    (2)
```

This is the exact missing implication between Taller--Vidick
near-completeness and algebraic nontriviality of `J`.

## 2. The recursion-theorem fork

Let a fixed-point machine `M_*` construct its Taller--Vidick LCS `L_*`,
enumerate formal proofs of `J_*=1`, and halt when it finds one.

* If `M_*` does not halt, completeness of proof enumeration gives
  `J_*!=1`.  Taller--Vidick's NONHALT soundness bounds the quantum value by a
  constant below one.  The standard perfect-LCS-gap theorem then makes the
  solution group nonhyperlinear.  This branch closes perfectly.
* If `M_*` halts after finding `D`, the source is a HALT instance.  The paper
  supplies `omega_q(L_*)>=1-epsilon`, while (1) supplies
  `omega_q(L_*)<=1-gamma(L_*,D)`.  There is no contradiction unless (2)
  happens to hold.

Changing the stopping rule to "halt only when a proof satisfying (2) is
found" does not help.  On failure to halt one can conclude only that no proof
crossed the chosen threshold, not that no proof of `J=1` exists.  The logical
step needed for the successful NONHALT branch is then lost.

This is precisely why threshold-free reverse Kleene works for Fanizza-style
**qualitative algebraic survival** but not for a one-shot approximate
completeness statement.

## 3. Why taking `epsilon` to zero is algebraically discontinuous

Definition 4.1 samples a mask function `mu` by choosing, independently for
every point `y`,

```text
mu(y)=1 with probability 1-epsilon,
mu(y)=-1 with probability epsilon.                        (3)
```

For every `0<epsilon<1`, every mask function has positive probability and
hence every corresponding LCS equation lies in the support.  At
`epsilon=0`, only `mu=1` remains.  Solution groups remember supported
equations, not their probabilities, so the presentation jumps at zero; it is
not an algebraic limit of the positive-noise presentations.

The analytic proof jumps at the same point.  Proposition 4.1 concludes

```text
omega_q(source^tensor-u) >= 4 epsilon delta^2,            (4)
```

using the Fourier factor `(1-2epsilon)^|beta|` and the inequality

```text
|beta|^(-1/2) >= (4epsilon)^(1/2)(1-2epsilon)^|beta|.
```

At zero, (4) is vacuous.  Theorem 5.2 also chooses `u=u(epsilon)` so that a
parallel-repetition value is below `4epsilon delta^2`; the output question
set therefore changes with `epsilon`.

For fixed `u`, positive `epsilon` gives the same support but increasingly
singular weights.  If `N` independent mask bits are sampled, the rarest mask
has probability at most `epsilon^N`.  A formal derivation of `J=1` may use an
equation carrying such a weight, so the game-value gap extracted from that
derivation can shrink much faster than the honest completeness loss
`epsilon`.  Uniformizing the mask equations removes the small weight but
makes the honest acceptance of the mask check only one half, destroying
near-perfect completeness.

## 4. What would actually make the diagonal work

A sequence of outputs `(L_k,J_k,epsilon_k)` with `epsilon_k ->0` would be
enough only with a new effective transfer theorem of the form

```text
J_k=1 with proof D
  => for some computable l>k, J_l=1 with transferred proof D_l
     and epsilon_l<gamma(L_l,D_l).                        (5)
```

The published reduction gives neither homomorphisms between the solution
groups at different repetition counts nor control of the transferred proof
gap.  Without (5), dovetailing the `k`-instances is the same uncrossed
triangular-array problem already isolated in the general reverse-Kleene
audit.

Hence recursion alone does not upgrade
`LIN*_(1-epsilon,s)=RE` to `epsilon=0`.  A successful construction must add
one of:

1. exact HALT-side algebraic survival of `J`;
2. a uniform HS/qa gap for every derivation of `J=1`; or
3. a nested solution-group transfer satisfying (5).

Each is genuinely new groupification or stability content.  None is a
formal consequence of Taller--Vidick's theorem.

