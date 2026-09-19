# Path-shaped PVMs classicalize without an outcome-count loss

Date: 2026-08-14

## 1. Outcome

The growing number of whole-map outcomes is not an extra simultaneous
rounding gate. Suppose `(P_i)_(i in I)` and `(Q_j)_(j in J)` are finite PVMs
in a finite tracial matrix algebra `(M,tau)`, and put

```text
C(P,Q)=sum_(i,j) ||[P_i,Q_j]||_2^2.                 (PCR1)
```

There is a PVM `(Q'_j)_(j in J)` such that every `Q'_j` commutes with every
`P_i` and

```text
sum_j ||Q'_j-Q_j||_2^2 <= 5 C(P,Q).                 (PCR2)
```

The constant is independent of `|I|`, `|J|`, and the matrix dimension. The
first PVM is left unchanged.

Consequently, let `P0,P1,Q0,Q1` be four finite PVMs and define the three
path-edge energies

```text
C00=C(P0,Q0),   C01=C(P0,Q1),   C11=C(P1,Q1).       (PCR3)
```

They can be replaced by PVMs `P0,P1',Q0',Q1'` satisfying the exact path
relations

```text
[P0,Q0']=0,   [P0,Q1']=0,   [P1',Q1']=0,            (PCR4)
```

and

```text
d_2(Q0,Q0')^2 <= 5 C00,
d_2(Q1,Q1')^2 <= 5 C01,
d_2(P1,P1')^2
  <= 5 (sqrt(C11)+sqrt(10 C01))^2.                  (PCR5)
```

Here `d_2(S,T)^2` is the sum of the squared Hilbert--Schmidt distances of
corresponding outcomes. Thus vanishing total commutator energy on the three
edges gives exact edgewise commuting PVMs after a cardinality-free `o(1)`
perturbation.

This closes the simultaneous-rounding clause in
`TRUE_EDGE_PVM_LOCALITY_CRITERION.md`. It does **not** prove that the atlas
transition PVMs have vanishing edge energies `(PCR3)` or that their outcomes
obey the Leavitt multiplication table. Those are now the only live
classicalization inputs.

## 2. One-edge proof

For every `i,j`, define the positive contraction

```text
A_ij=P_i Q_j P_i.                                    (PCR6)
```

For fixed `i`, `(A_ij)_j` is a POVM in the corner `P_i M P_i`, because

```text
sum_j A_ij=P_i.                                      (PCR7)
```

The projection compression identity gives

```text
tau(A_ij-A_ij^2)=(1/2)||[P_i,Q_j]||_2^2.            (PCR8)
```

Apply de la Salle's cardinality-free POVM orthogonalization theorem inside
each nonzero corner, with its normalized trace. It produces a PVM
`(R_ij)_j` summing to `P_i` and, after rescaling the corner traces and
summing over `i`,

```text
sum_(i,j) ||R_ij-A_ij||_2^2
 <=(9/2) C(P,Q).                                    (PCR9)
```

Set

```text
Q'_j=sum_i R_ij.                                    (PCR10)
```

The different `i`-corners are orthogonal, so `(Q'_j)_j` is a PVM and it
commutes with every `P_i`. Let

```text
E_P(X)=sum_i P_i X P_i.                              (PCR11)
```

Then `E_P(Q_j)=sum_i A_ij`. The difference
`Q'_j-E_P(Q_j)` is block diagonal for `(P_i)`, whereas
`E_P(Q_j)-Q_j` is orthogonal to the block-diagonal algebra in `L^2(M,tau)`.
Consequently

```text
sum_j ||Q'_j-Q_j||_2^2
 =sum_(i,j)||R_ij-A_ij||_2^2
   +sum_j||E_P(Q_j)-Q_j||_2^2.                      (PCR12)
```

The standard PVM commutator identity is

```text
sum_i ||[P_i,X]||_2^2
 =2||X-E_P(X)||_2^2                                 (PCR13)
```

for self-adjoint `X`. Applying it to every `Q_j` makes the second term in
`(PCR12)` equal to `C(P,Q)/2`. Combining this with `(PCR9)` proves `(PCR2)`.

There is no hidden minimum atom mass: the corner theorem is multiplied by
`tau(P_i)` before summing, and zero corners are simply omitted.

## 3. The three-edge path

First apply the one-edge theorem to `(P0,Q0)` and `(P0,Q1)`. This leaves
`P0` fixed and gives `Q0',Q1'` satisfying the first two relations in
`(PCR4)` and the first two estimates in `(PCR5)`.

It remains to classicalize `(Q1',P1)` while keeping the already repaired
`Q1'` fixed. In the Hilbert direct sum indexed by both outcomes, the triangle
inequality and `(PCR13)` give

```text
sqrt(C(P1,Q1'))
 <=sqrt(C11)+sqrt(2) d_2(Q1,Q1')
 <=sqrt(C11)+sqrt(10 C01).                          (PCR14)
```

Apply `(PCR2)` with `Q1'` as the PVM to be kept and `P1` as the PVM to be
changed. This proves the last relation in `(PCR4)` and the last estimate in
`(PCR5)`. No commutation is needed on the unused edge `(P1,Q0)`.

## 4. Exact Fourier source of total commutator energy

There is also no Fourier alphabet loss before `(PCR1)`. Let
`rho:A->U(M)` and `sigma:B->U(M)` be exact representations of finite
abelian groups, with character PVMs `(P_chi)` and `(Q_psi)`. Operator-valued
Parseval on `A x B` gives the exact identity

```text
(1/(|A||B|)) sum_(a,b) ||[rho(a),sigma(b)]||_2^2
 =sum_(chi,psi)||[P_chi,Q_psi]||_2^2.               (PCR15)
```

Indeed

```text
[rho(a),sigma(b)]
 =sum_(chi,psi) chi(a) psi(b) [P_chi,Q_psi],        (PCR16)
```

and the scalar characters of `A x B` are orthonormal. Thus a group packet
which supplies averaged commutation of two complete finite abelian root
subgroups automatically supplies the total spectral-PVM energy needed by
the one-edge theorem.

Care is still required after arbitrary deterministic coarsening: `(PCR15)`
applies directly to spectral PVMs (and to restriction/quotient spectral
PVMs), not to an arbitrary decoder with no quantitative stability proof.
Exact commuting PVMs may of course be coarsened freely.

## 5. Correct remaining gate

The path criterion can now be used in the following sharper form:

> Construct the four whole-map PVMs for the paired radical quotient and
> prove that the three total edge energies `C00,C01,C11` tend to zero, while
> their three trace laws have vanishing diagonal/crossed Leavitt mismatch.

The theorem above then makes the edge commutation exact with no dependence
on the growing number of maps. Tree gluing supplies the common latent law,
and the robust `1/36` paired-quotient floor gives the contradiction.

The local Pauli model remains the obstruction to the missing premise: its
incompatible spectral PVMs have nonzero total commutator energy. The raw
routing/four-root packet must therefore force `(PCR3)` to vanish; PVM
rounding itself is no longer part of the open problem.
