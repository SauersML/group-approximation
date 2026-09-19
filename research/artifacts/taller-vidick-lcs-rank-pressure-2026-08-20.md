# Taller--Vidick 3-LCS audit and Clifford rank-pressure interface

Date: 2026-08-20

Primary source: Aviv Taller and Thomas Vidick, *Approximating the quantum
value of an LCS game is RE-hard*, arXiv:2507.22444v2.

Companion source: Connor Paddock and William Slofstra, *Satisfiability problems
and algebras of boolean constraint system games*, arXiv:2310.07901v2.

Incidence source: Honghao Fu, Kieran Mastel, and Xingjian Zhang, *Succinct
Perfect Zero-knowledge for MIP\**, arXiv:2503.04517v2, Theorem 3.1.

## Imported results

The test samples an independent mask `mu`, sets `g'=f g mu`, and tests one
three-variable parity equation.  Proposition 4.2 proves

```text
value(L^epsilon)>=1-(1-delta)^2/36
  => value(source^tensor-u)>=4 epsilon delta^2.
```

Lemma 4.3 gives completeness `1-epsilon` from a perfect synchronous source.
Theorem 5.3 chooses `delta=1-1/sqrt(2)` and obtains synchronous soundness
`71/72` for every rational `0<epsilon<1/72`; the answers have length three.
Remark 5.4 obtains an unrestricted quantum-value hardness statement because
the output is a projection game.

The same mask is responsible for both sides: honest loss occurs at
`mu(phi)=-1`, and soundness uses the Fourier multiplier
`(1-2 epsilon)^|beta|`.  Setting `epsilon=0` deletes the damping.  The source
therefore does not provide the perfect LCS gap needed by the ordinary solution
group construction.

## New interface

Every output constraint is

```text
x_1+x_2+x_3=b.
```

Its violation bit `v=b+x_1+x_2+x_3` is affine, and

```text
rank diag(1,v)=1+v.
```

Thus the whole output menu uses one fixed two-pair Clifford packet.  The noisy
check is not imposed; its failure is retained as a full `M_4` block rather
than rejected from the algebra.  A satisfying atom has two `M_2` packet
types, while a violating atom has one `M_4` type, and restriction to the
baseline Pauli pair records the one-versus-two relative multiplicity.

This is a genuine bypass of the *local* perfect-completeness obstruction:
the controlled Pauli construction exists exactly on every selector atom.  It
is not yet a nonhyperlinear group.  A finite presentation must return the
uniform packet so that the finite-dimensional type deficit pays normalized-HS
energy, while an exact tracial model with the distinguished phase survives.

## Comparison with the Fanizza lane

The Fanizza route has an exact nonlinear Turing BCS and a polynomial
computation recurrence, but needs S3 radical charts and selector renewal.  The
Taller--Vidick route has a direct constant game-value gap and only affine
three-XOR checks.  Its price is that exact completeness must be recovered by
the rank-pressure incidence rather than inherited from the LCS game.  The two
routes now meet at the same sharply isolated theorem: a tracially exact,
finite-dimension-obstructed fixed-scale multiplicity return.

## Tracial source and exact failure projection

Paddock--Slofstra Definition 3.1 and Lemma 3.4 give

```text
1+P_R(U)=2 sum_(phi notin R) Pi_(U,phi).
```

Their Theorem 3.11 identifies a tracial state with perfect commuting play and
an `R^U` representation with perfect quantum-approximable play.  Example 4.2
therefore supplies a fixed perfect tracial BCS whose finite game value is
bounded below one.

Fu--Mastel--Zhang now close this source-interface gap.  From a
constraint--constraint BCS game `G`, their Theorem 3.1 constructs a synchronous
constraint--variable game `G^cv`.  Its sampled pairs are only `(i,i)`, `(x,x)`,
`(i,x)`, and `(x,i)` for `x` contained in context `i`.  Their quantitative
soundness implies

```text
omega_qa(G)<1  =>  omega_qa(G^cv)<1.
```

The paper states finite-dimensional PCC completeness, so we do not cite it for
the commuting-operator extension.  Instead the Paddock--Slofstra trace supplies
that extension directly.  With context atoms `P_(i,a)` and variable
projections `E_(x,b)`, incidence gives

```text
P_(i,a) E_(x,b)=1_(a_x=b)P_(i,a).
```

Thus all sampled PVM pairs commute and the correlation
`tau(P^q_a P^r_b)` wins perfectly.  Unrelated contexts are never paired.  This
establishes Cairn's `oracularizable-tracial-nonru-game-exists`; generic
projection of two unrelated contexts remains invalid.

With that source interface established, one must still not replace a
near-perfect LCS strategy by a shared exact variable
tuple: Alice has commuting context observables, Bob has shared query
observables, and their disagreement is part of the loss.  For a verifier round
let `r_par` be Alice's three-XOR parity failure and `r_con` the selected
Alice--Bob equality failure.  Both are affine and the round loses iff at least
one is one.  Therefore a value bound `s<1` forces
`E(r_par+r_con)>=1-s`.  A controlled packet has its extra rank exactly on each
failure projection in the Paddock--Slofstra identity.  Hence source existence,
exact local tracial lift, and positive finite-dimensional pressure are
established before the global endpoint-alignment and return theorem.
