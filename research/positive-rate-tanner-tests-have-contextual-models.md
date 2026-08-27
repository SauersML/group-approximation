---
rg: 2
id: positive-rate-tanner-tests-have-contextual-models
kind: claim
title: Positive-rate bounded-local linear tests have exact class-two contextual models
distinct_from:
  local-exterior-square-kernel-yields-pauli-strategy: that uses one decomposable exterior square and one qubit; this uses the whole class-two commutator quotient and gives a constant average obstruction by dimension.
  signed-character-expansion-decodes-operator-parallelograms: that succeeds for a bounded-dimensional character code; this rules out the positive-rate auxiliary Tanner code as the preceding operator-agreement layer.
---

ESTABLISHED.  Let `E` be `N` binary coordinates and let
`{S_j}_{j in J}` be local contexts with

```text
|J| <= D N,              |S_j| <= q.                       (PRC1)
```

Give each context a binary linear code `C_j <= F_2^{S_j}` and let

```text
C={u in F_2^E : u|S_j in C_j for every j},   dim C=k.      (PRC2)
```

There is an exact finite-dimensional reflection strategy satisfying every
local codeword-PVM test and every overlap-consistency test for which

```text
E_(s,t in E)||[Q_s,Q_t]||_2^2
 >= 4/N^2 (binom(k,2)-|J| binom(q,2)).                     (PRC3)
```

Consequently every globally commuting reflection table `{P_s}` satisfies

```text
E_s ||Q_s-P_s||_2^2
 >= 1/(4N^2) (binom(k,2)-|J| binom(q,2)).                  (PRC4)
```

If `k>=rho N` while `D,q` are fixed, both lower bounds are positive constants
for all sufficiently large `N`.  Thus no positive-rate bounded-locality
linear Tanner code has a same-Hilbert operator agreement theorem based only
on exact local codeword measurements and their shared-coordinate or
shared-overlap consistency, even when its classical agreement, distance, and
cosystolic expansion are excellent.

This applies directly to the positive-rate left-right Cayley LTC of
[Dinur--Evra--Livne--Lubotzky--Mozes](https://arxiv.org/abs/2111.04808): if
the generator degree is `Delta`, then the coordinates are the squares,
every vertex context has size `Delta^2`, and there are
`4N/Delta^2` vertex contexts.  Running the
[augmented quantum tensor-code test](https://arxiv.org/abs/2111.08131) of
Ji--Natarajan--Vidick--Wright--Yuen inside every fixed-size vertex view does
not repair the outer test.  The strategy in `(PRC3)` already has one exact
codeword PVM at every vertex, so all of its point, line, augmentation, and
overlap measurements are compatible coarsenings and pass perfectly.  The
quantum Tanner code distance theorem likewise does not constrain this
class-two quotient.

The obstruction gives a sharp design requirement.  Before a bounded-template
operator agreement decoder can exist, either the global abelianized section
dimension must be reduced to

```text
k = O(sqrt(N)),                                             (PRC5)
```

or the test must add enough algebraic transport to kill the full exterior
square without listing `Omega(k^2/q^2)` independent local jointness
directions.  The affine simplex target is on the feasible side:
`k=n+1` and `N=2^n`.  The established signed-character decoder is also on the
feasible side because its bare left-right character code has bounded `k`.
Hence the correct composition order is to collapse the auxiliary proof
system to the low-dimensional simplex section first and only then invoke
signed-character/operator-parallelogram decoding; a positive-rate Tanner
ambient code cannot itself perform that collapse operatorially.
