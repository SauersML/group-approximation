# Relative rank-one Schur--Clifford/Fanizza synthesis

**Date:** 2026-08-20  
**Status:** three local theorems proved, one finite search completed on MSI,
and the exact groupification interface isolated.  This is not a proof of a
nonhyperlinear group.

## 1. The normalized support compiler

For the forbidden support atom "child `f` survives while parent `e`
disappears", the raw Steinberg matrix `[[e,f],[f,f]]` has ranks `0,2,1,1` on
`(00,01,10,11)`.  It detects the right atom, but has no fixed baseline pivot.
The rank-normalized replacement is

```text
M_sub(e,f) = [[1,1+e],[f,0]],
det M_sub = (1+e)f,
rank M_sub = 1+(1+e)f.
```

This is the exact relative-rank-one object wanted by the groupification route:
the leading `[1]` gives one fixed Pauli simple on every selector assignment,
and only `(0,1)` adds another Pauli coordinate.

## 2. MSI exhaustion

`experiments/minimal_rank_one_support_compiler.py` was synced to the shared
project checkout and run directly through the MSI wrapper on `acn112` with
`/usr/bin/python3.11`.  It used one process, 0.10 seconds wall time and 12,152
KiB maximum RSS.  No scheduler job was submitted and no process remained.

The exact search over all `8^4=4096` affine two-by-two matrices returned:

```text
all rank-profile (1,2,1,1) compilers: 252
compilers with upper-left entry identically 1: 24
minimum complexity: (3 nonzero entries, 4 affine monomials)
minimum fixed-pivot complexity: (3,4)
sparsest fixed-pivot compilers: 4
chosen: [[1,1+e],[f,0]]
```

The same script exactly diagonalizes the baseline intertwiner Laplacian in the
Pauli-word basis and returns `kappa=4`.

## 3. The concrete finite packet

The class-two group `B_sub=K(M_sub)` has order 128.  Its fixed-pivot subgroup
`A_sub` has, after fixing `J=-1` and the two selector signs, one simple module
of dimension two.  A full `B_sub` simple has dimension two on allowed atoms and
four on the forbidden atom, so restriction multiplicity is respectively one
and two.

For `S={p_1,q_1,z_e,z_f}`, the pairwise Laplacian spectra on the four baseline
selector types are `4h, 4+4h, 4+4h, 8+4h`, where `h` is selector Hamming
distance.  Thus the positive gap is exactly four and the general
multiplicity-payment theorem gives `transport energy >=2L/d`.  Payment is no
longer the missing theorem.

## 4. Why rank one changes the no-signaling obstruction

For the three endpoint-sharing laws, write their shared Bernoulli marginals as
`a,b`.  Diagonal failure is at least `1-a` and `1-b`; crossed failure is at
least `max(0,a+b-1)`.  Their sum is at least one.  After uniform averaging over
the four source pairs, the error sum is at least `1/4`, so one context has error
at least `1/12`.

The exact counterbox in `notes/FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md`
needs binary pairing rank at least two.  It cannot live on this one-bit
relative packet.  What remains is to prove that approximate group words really
expose the same relative bit at all three endpoints.

## 5. Precise Fanizza import and a necessary correction

Definition 4.1 and Theorem 4.4 of Fanizza--Kroell--Mehta--Paddock--Rochette--
Slofstra--Zhao, arXiv:2510.04943, provide a computable Turing BCS family and
`m notin L => phi(D) <= C_m epsilon` for every epsilon-perfect strategy.
Proposition 5.14 supplies a polynomial relator-ideal decomposition of

```text
P_tilde_n + X_tilde_n P_tilde_n X_tilde_n - P_tilde_(n+1)=0.
```

The paper obtains signal collapse by exponentially weighted summation of those
polynomial costs.  It does not literally state the scalar fixed-contraction
recurrence sometimes used to summarize the mechanism.

More importantly, on the nonmember side a perfect strategy has `phi(D)=0`.
Therefore `D` is not itself the separated nonhalting mark.  A valid group route
must connect a separate nontrivial Boone/self-referential word to the initial
relative-Pauli carrier.  This is now an explicit clause of
`relative-rank-one-fanizza-groupification`.

## 6. Remaining theorem

The remaining theorem is finite and quantitative:

1. replace each nonlinear support primitive by the 128-element packet above;
2. keep selector phases context-local rather than globally central;
3. exactify the packets in normalized HS norm;
4. expose the same one-bit relative coordinate at the three shared endpoints;
5. make each rank-one failure a fixed group-relator defect;
6. preserve the Fanizza polynomial/exponential accounting; and
7. feed the initial carrier from a separate genuinely nontrivial group word.

If these seven clauses hold with a universal local constant, the existing
`hs-pcp-boone-compiler` fixed-point route produces a nonhyperlinear group.

The decisive falsification test remains the classical-CSP substitution: a
compiler argument that still works after making every selector globally
commuting is wrong, because finite graphs of finite groups are hyperlinear.
