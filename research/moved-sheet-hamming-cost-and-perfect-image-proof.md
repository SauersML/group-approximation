---
rg: 2
id: moved-sheet-hamming-cost-and-perfect-image-proof
kind: route
title: A moved sheet costs a fixed trace fraction
target: four-sheet-monomial-mixing-reduces-to-commutant
requires:
  - pauli-swap-coherence-reduces-to-the-commutant-gate
---

Products and inverses of block-monomial unitaries are block monomial.
Because `A_s` and `D_s` are block diagonal, the sheet permutation of a
word `q(U)` is exactly the word permutation

```text
p(q)=q((p_s)_(s in Sigma)) in S_k.                      (MSH1)
```

Let `V` be a block-monomial unitary and suppose its permutation moves
exactly `m` sheets. For a vector `xi in H_j` on a moved sheet,
`Vxi` belongs to the orthogonal sheet `H_(p(j))`. Therefore

```text
||(V-I)xi||^2=||Vxi||^2+||xi||^2=2||xi||^2.
```

Using equal sheet dimensions and discarding the nonnegative contributions
of fixed sheets gives

```text
||V-I||_2^2 >= 2m/k.                                   (MSH2)
```

Every nonidentity permutation moves at least two points. Thus

```text
p(q) != 1  implies  ||q(U)-I||_2 >= 2/sqrt(k).          (MSH3)
```

Under `(FSM2)`, equation `(MSH3)` forces `p(r)=1` for every defining
relator. Hence the generator assignment `s|->p_s` descends to the
homomorphism `(FSM3)`.

The group `G=EL_28(J)` is perfect by the elementary commutator identity

```text
x_ij(a)=[x_ik(a),x_kj(1)]
```

for distinct `i,j,k`. The image of a perfect group under any homomorphism
is perfect. For `k<=4`, the symmetric group `S_k` is solvable, and every
subgroup of a solvable group is solvable. A group that is both perfect and
solvable is trivial: its derived series is constant at the group by
perfectness but must terminate at the identity by solvability. Therefore
the image of `(FSM3)` is trivial, so `p_s=1` for all `s`.

Equation `(FSM1)` now reads `Z_s=D_s`, which lies in `rho(F_N)'` by
hypothesis. The previously proved commutant-coherence theorems apply.

For `k=5` the counting estimate `(MSH3)` still makes the permutation
assignment exact, but `S_5` contains the perfect subgroup `A_5`. This is
only the first group-theoretic possibility; no `A_5` quotient of `G` is
claimed.
