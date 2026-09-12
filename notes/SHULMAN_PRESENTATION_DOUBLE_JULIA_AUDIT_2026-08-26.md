# Shulman's presentation-double construction: exact Julia normal form

Date: 2026-08-26

## Question

Does the proof of Shulman's symmetric-amalgam MF theorem supply block,
intertwiner, or rank data that closes the open
`leavitt-positive-rank-intertwiner-retention` condition for

```text
Q=F/K,                    P=F *_K F,
```

where `F` is finitely generated free and `Q` is the simple nonsofic binary
Leavitt quotient?

## Answer

It supplies one useful exact normal form, but no trace-visible rank.

Because the vertex is free, the vertex lift in Shulman's proof can be chosen
coordinatewise exact.  Her fixed Julia stabilization then gives the two
finite-dimensional vertex representations as

```text
v_n=sigma_n,
u_n=V_n^* sigma_n V_n.
```

Thus they are not arbitrary unstable pairs: they are globally conjugate.
Their convergence on `K` is exactly

```text
||[sigma_n(k),V_n]||_op -> 0,
```

and separation at `f_0` is exactly an operator-norm-visible commutator with
the same `V_n`.

Multiplication by `V_n` identifies the left-right representation with
`Ad(sigma_n)`.  Since the quotient `Q` has no nontrivial finite-dimensional
unitary representations, restriction rigidity implies

```text
sigma_n(K)'=sigma_n(F)'.
```

Consequently the exact zero eigenspace of every kernel-intertwiner Laplacian
is already fixed by all of `F`.  The desired nontrivial quotient sector must
come from positive eigenvalues converging to zero, not from the exact
intertwiner space.

This is the useful structural conclusion: the open problem is a collapsing
adjoint spectral-gap problem for a single exact representation and one
almost-`K`-central Julia unitary.

The negative conclusion is equally sharp.  Lemma 9 uses a quasicentral
approximate-unit cutoff and only controls operator norm.  It gives no trace
of the cutoff and no multiplicity of a low-energy band.  The stabilization
factor is the fixed number four, but the selected inner coordinate is
uncontrolled.  Arbitrarily large common exact summands can be inserted in
the escaping tail without altering the strong quotient, edge error, or
operator separation.  Therefore the source proof itself yields no
normalized-rank retention.

## Primary source pin

Tatiana Shulman, *The MF property for amalgamated free products*,
arXiv:2603.13564v2, Lemmas 7--9 and Theorem 10.  The relevant displayed
formula is

```text
phi_k^(2)=phi_k directSum phi_k,
phi_k^(1)=V_k^* phi_k^(2) V_k.
```

The result is wired into Cairn as
`shulman-presentation-double-witnesses-have-adjoint-normal-form`.
