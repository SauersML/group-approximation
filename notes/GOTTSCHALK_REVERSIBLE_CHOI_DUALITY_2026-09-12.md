# Infinite conditional-entropy duality fails for a reversible CA Choi state

Date: 2026-09-12. This is an exact test of the pure-Choi entropy argument
currently being considered for Gottschalk's conjecture. It does not solve
Gottschalk's conjecture. It shows that global purity and a bounded local
quantum decoder do not justify complement duality after infinite
conditioning. The conditioner contains whole reference/output sites, not
selected individual qubits. The masks below are deterministic; an iid-mask
assertion requires a separate argument.

The computation was independently audited by the operator-algebras agent.
No numerical computation or enumeration was used.

## A reversible square cellular automaton

Let `G=Z x C2`, write its elements as `(n,i)`, and set

```
G_0 = Z x {0},       G_1 = Z x {1},       e=(0,0).
(Lf)(n,i) = f(n,1-i)+f(n+1,1-i)          over F_2.
J(a,b) = (a,b+La).
```

There are two classical bits at each site. Since the field has
characteristic two, `J^2=id`. Thus this is a reversible, finite-memory,
equal-alphabet CA over an amenable group.

Put two reference qubits `R_g` and two output qubits `B_g` at each site.
Start with independent EPR pairs between the corresponding reference and
output qubits, and implement `J` on the outputs by controlled-NOT gates.
All these gates have an output first-track control and an output
second-track target. They commute and have uniformly bounded overlap;
alternatively they can be arranged in finitely many disjoint-gate layers.
They define a quasilocal automorphism. Its image of the product EPR state
is therefore pure and translation invariant. Applying the same circuit
again decodes it. In particular the state has the full local quantum
recovery property, not only a classical left inverse.

Both its entire reference marginal and its entire output marginal are
the product trace. This follows for the output from the trace-preserving
quasilocal automorphism, and for the reference because the circuit acts
on the outputs alone.

## Finite stabilizers and the entropy calculation

For finitely supported pairs of bit functions `p=(a,b)` and `q=(c,d)`,
the CSS stabilizers of this Choi state are

```
X_R(p) X_B(Jp),
Z_R(J^T q) Z_B(q),
```

where `J^T(c,d)=(c+L^T d,d)`. These describe all finite-support
stabilizers: the inverse Clifford circuit takes every finite Pauli
operator back to a finite Pauli operator in the product EPR state.

For a finite set `W` of individual qubits, let `r(W)` be the binary
dimension of its supported stabilizer space. Its reduced density matrix
is the normalized projection onto the simultaneous `+1` eigenspace of
these stabilizers, so

```
S(W) = |W|-r(W)                                      (bits).
```

Let `A=R_e`, which consists of two qubits. For an arbitrary set `U` of
other qubits, use the usual finite-conditioner definition

```
S(A|U) = inf_{K finite subset U} [S(AK)-S(K)].
```

Adding `A` changes the stabilizer rank by the dimension of the image of
the supported stabilizers on `A`: stabilizers with zero restriction to
`A` are exactly those already supported on `K`. The CSS form allows the
X and Z increments to be counted separately.

Define the complementary infinite conditioners

```
U = R_(G_0 minus {e}) union B_(G_0),
V = R_(G_1) union B_(G_1).
```

Their union is every qubit other than `A`.

### Conditioning on U

An X stabilizer supported in `A union U` has `a,b` supported in `G_0`.
Its output also lies in `G_0`, forcing `La=0` on `G_1`. The finite-support
kernel of the difference operator `1+s` on `Z` is zero, so `a=0`.
The only possible nonzero root X coordinate is therefore `b(e)`.
It is achieved by the stabilizer pairing the second reference and output
qubits at `e`.

For Z stabilizers, `c,d` are supported in `G_0` and `L^T d=0` on `G_1`.
Again `d=0`. The only root Z coordinate is `c(e)`, achieved by the
stabilizer pairing the first reference and output qubits at `e`.

Thus the root rank increment is at most two for every finite conditioner
in `U`, and is exactly two as soon as that conditioner contains `B_e`.
Consequently

```
S(A|U) = 2-2 = 0.
```

### Conditioning on V

For an X stabilizer supported in `A union V`, its first output track
forces `a(e)=0`, hence `a` is supported in `G_1`. Its second output track
forces

```
(La)|_(G_0) = b(e) delta_e.
```

The image of any finitely supported function under `1+s` has even total
parity. It cannot equal a single delta. Therefore `b(e)=0` as well, and
there is no X rank increment at the root.

The transposed calculation gives no Z rank increment: `d` is supported
in `G_1`, and the first reference track would require `L^T d` to equal
a single delta on `G_0` if it had a nonzero root coordinate. The same
parity argument forbids this.

Every finite conditioner in `V` therefore has zero root rank increment.
It follows that

```
S(A|V) = 2.
```

We have proved the strict failure

```
S(A|U)+S(A|V) = 2 bits,
```

despite global purity, reversible square-CA origin, finite-depth
preparation, full local quantum recovery, and whole-site conditioning.

## Why finite-dimensional duality does not pass to this limit

On a finite cyclic version of the same construction, constant vectors
are finite-support vectors in the kernel of `1+s`. The resulting global
stabilizers supply the missing root increments, restoring ordinary
finite-dimensional entropy duality. On the infinite group, those
constant vectors have infinite support and do not belong to any finite
observable algebra. Interchanging the infinite-volume limit with
conditioning on an entire half of the system discards exactly these
stabilizers.

The identity `S(A|U)=-S(A|V)` is therefore not a consequence of pure
state preparation alone in the finite-conditioner definition above.
The same is true after assuming the local full quantum decoder.

## Boundary of the counterexample

The two masks are layer masks, not independent Bernoulli masks.
Randomizing their common layer label gives an invariant correlated mask
law, still not an iid law. Thus this example does not by itself refute
an iid-averaged duality theorem. Such a theorem would need to eliminate
the infinite conditional modes probabilistically, rather than invoking
purity or local recovery as sufficient premises.

The CA `J` is an involution and hence surjective. This control is not a
counterexample to Gottschalk's conjecture and is not a new proof route
for the universal claim.
