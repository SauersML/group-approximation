---
rg: 2
id: cubic-occurrence-splitting-tietze-proof
kind: route
title: Tietze-eliminate cyclic equality copies in a binary LCS
target: cyclic-occurrence-splitting-makes-every-lcs-cubic
requires:
  - degree-two-operator-ports-are-boundary-edges
---

# Tietze-eliminate cyclic equality copies in a binary LCS

## 1. Construction

Let `L` be a finite binary LCS with solution group

$$
\Gamma_L=
\left\langle J,(x)_{x\in X}
\ \middle|\begin{array}{l}
J^2=x^2=1,\quad[J,x]=1,\\
[x,y]=1\quad\text{when }x,y\text{ occur in one equation},\\
\displaystyle\prod_{x\in C}x=J^{b_C}\quad(C\in\mathcal C)
\end{array}
\right\rangle .                                      \tag{1}
$$

Count one occurrence of a variable per equation.  For every `x` occurring
`d_x\geq3` times, order those occurrences arbitrarily and introduce copies

$$
x^{(1)},\ldots,x^{(d_x)}.
$$

Use `x^{(i)}` in the `i`th old equation and add `d_x` new even equations

$$
x^{(i)}x^{(i+1)}=1
\quad(1\leq i\leq d_x),
\qquad
x^{(d_x+1)}:=x^{(1)}.                                  \tag{2}
$$

Variables of occurrence at most two are unchanged.  Call the resulting
system `L^{(3)}`.

Every new copy appears once in an old equation and in the two neighboring
equations of (2), hence exactly three times.  Unchanged variables still
occur at most twice.  The construction adds a number of variables and
equations linear in the input's total occurrence count.

## 2. Equality equations are literal identifications

In the solution group of `L^{(3)}`, an equation from (2) gives

$$
x^{(i)}x^{(i+1)}=1.
$$

Both generators are involutions, so

$$
x^{(i)}=(x^{(i+1)})^{-1}=x^{(i+1)}.                    \tag{3}
$$

The context commutator
`[x^{(i)},x^{(i+1)}]=1` is automatic after (3).  Going around the cycle,

$$
x^{(1)}=x^{(2)}=\cdots=x^{(d_x)}.                     \tag{4}
$$

Thus all but one copy can be removed by elementary Tietze transformations.

## 3. Explicit inverse homomorphisms

Define

$$
\Phi:\Gamma_{L^{(3)}}\longrightarrow\Gamma_L
$$

by `\Phi(J)=J`, by sending every unchanged variable to itself, and by

$$
\Phi(x^{(i)})=x.
$$

Every old equation maps to its original equation, every old context
commutator maps to the corresponding original commutator, and (2) maps to
`x^2=1`.  Hence `\Phi` is well defined.

Conversely, define

$$
\Psi:\Gamma_L\longrightarrow\Gamma_{L^{(3)}}
$$

by `\Psi(J)=J`, leaving unchanged variables fixed, and setting

$$
\Psi(x)=x^{(1)}
$$

for a split variable.  In an original equation, the relevant copy might be
`x^{(i)}` rather than `x^{(1)}`, but (4) identifies them.  The same
observation transfers every original context commutator.  Thus `\Psi` is
well defined.

Clearly `\Phi\Psi` is the identity.  Equation (4) shows that
`\Psi\Phi` fixes every copied generator as well, so

$$
\boxed{\Gamma_{L^{(3)}}\cong\Gamma_L}
$$

and the isomorphism fixes `J`.

## 4. Sharpness and quantitative caveat

Paddock--Russo--Silverthorne--Slofstra identify the occurrence-two class
with graph-incidence systems and prove that the distinguished `J` survives
universally exactly when it survives in finite dimension
[Algebraic Combinatorics 6 (2023), Theorem 4.1 and Corollary
4.7](https://doi.org/10.5802/alco.292).  The construction above shows that
raising the maximum occurrence from two to three already accommodates
every binary LCS solution group.  Composing it with Slofstra's
[solution-group embedding](https://arxiv.org/abs/1606.03140) transfers the
full exact group-theoretic complexity to occurrence three.

This does not give a uniform robust compiler.  If the equations in (2) have
small Hilbert--Schmidt defects, telescoping from `x^{(1)}` to a remote
`x^{(i)}` costs the sum of the intervening equality defects.  With an
unbounded occurrence cycle, that loss is unbounded.  No constant-soundness
claim follows from the Tietze isomorphism alone.
