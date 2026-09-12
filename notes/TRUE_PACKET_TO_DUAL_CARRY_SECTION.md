# A determinant-one primal packet gives explicit equations for the dual carry section

Date: 2026-08-12

## 1. Outcome

The determinant-one level-`121` cycle packet does not itself bound the dual
carry sequence

```text
0 -> L -> M_Sigma -> Q^# -> 0.                              (PDS1)
```

It does, however, reduce the missing section to one exact integral right
inverse with only seven distinguished right-hand sides.  No nonlinear phase
lifting, modular SAT instance, or enumeration of the enormous harmonic
discriminant is needed.

In general, if integral cycles `c_1,...,c_r` project to a `Z`-basis of the
primal harmonic lattice `Q`, then

```text
K = S_sat directSum <c_1,...,c_r>_Z.                          (PDS2)
```

Let `u_1,...,u_r` be the basis of `Q^#` dual to the projected packet.  The
desired ambient integral lifts are exactly the solutions of

```text
<z_i,s> = 0       for every s in S_sat,
<z_i,c_j> = delta_ij.                                         (PDS3)
```

Equivalently, choose any primitive integral cycle basis `B` and any integral
right inverse `R` with `B R=I`.  If

```text
P=(<u_i,B_j>)_(i,j),                                          (PDS4)
```

then

```text
Z=(R P^T)^T                                                   (PDS5)
```

has rows `z_i` satisfying `(PDS3)` and is a `Z`-linear section of `(PDS1)`.
This gives a compact exact construction of the missing dual packet from the
already certified primal packet.

At level `121`, `r=7`, `rank(K)=632`, `rank(S_sat)=625`, and the ambient
dimension is `1940`.  The existing determinant-one packet therefore reduces
the full dual problem to seven rows of one right inverse for a
`632 x 1940` primitive lattice basis.  The exact implementation is

```text
experiments/sl3_projective_dual_section_from_packet.py.       (PDS6)
```

The first generic saturation attempt certified the rank decomposition and
constructed `S_sat directSum <c_i>` in `496.173` seconds, but its ten-minute
job cap expired during the subsequent integral right inverse.  This is a
performance result, not a mathematical obstruction.  The implementation now
uses the faster rational-kernel/intersection construction already validated
by the level-`121` systole computation.  A second attempt using the direct
integer kernel was stopped by its fifteen-minute cap before the kernel
finished.  The direct sparse packet equations subsequently bypassed both
normal-form bottlenecks and produced the complete rank-seven section with
norm at most `21.9892802607...`; see
`TRUE_N121_DUAL_CARRY_SECTION.md`.

## 2. Packet splitting theorem

Let `Lambda=Z^m`, let `K` be a primitive sublattice of `Lambda`, and let
`S_sat subset K` be primitive in its real span.  Put

```text
H=K_R intersect span_R(S_sat)^perp,
Q=P_H(K).                                                    (PDS7)
```

Suppose `c_1,...,c_r in K` and their harmonic projections form a `Z`-basis
of `Q`.

**Theorem 1 (primal packet splitting).**  One has the internal direct sum

```text
K=S_sat directSum C,       C=<c_1,...,c_r>_Z.                 (PDS8)
```

**Proof.**  The projection `P_H:K->Q` is surjective with kernel `S_sat`.
For `k in K`, expand `P_H(k)` uniquely as

```text
P_H(k)=sum_i n_i P_H(c_i),       n_i in Z.                    (PDS9)
```

Then `k-sum_i n_i c_i` belongs to `S_sat`, proving generation.  If a
combination of the `c_i` belongs to `S_sat`, its projection is zero, and
linear independence of the displayed basis forces every coefficient to
vanish.  End proof.

This explains the force of the determinant-one computation in
`TRUE_SQUARE_LEVEL_BOUNDARY_REDUCED_SECTIONS.md`: the index calculation is
exactly the integral hypothesis of Theorem 1, not merely a rational spanning
test.

## 3. Dual right-inverse theorem

Write a primitive basis of `K` as the rows of an integer matrix

```text
B in M_(k,m)(Z).                                               (PDS10)
```

Because `K` is primitive in the unimodular lattice `Lambda`, restriction of
integer functionals is surjective:

```text
Hom(Lambda,Z) -> Hom(K,Z).                                    (PDS11)
```

Equivalently, there is an integer matrix `R in M_(m,k)(Z)` satisfying

```text
B R=I_k.                                                       (PDS12)
```

Let `u_1,...,u_r` be the basis of `Q^#` dual to the packet, and let `P` be
the integral pairing matrix `(PDS4)`.

**Theorem 2 (packet-to-carry section).**  The rows of `Z` in `(PDS5)` lie in
`M_Sigma`, project respectively to `u_1,...,u_r`, and define an integral
section of `(PDS1)`.

**Proof.**  Equations `(PDS5)` and `(PDS12)` give

```text
Z B^T=P.                                                       (PDS13)
```

Thus the functional induced by row `z_i` on every element of `K` agrees
with the functional induced by `u_i`.  Orthogonal projection to `K_R`
preserves all pairings with `K`, so nondegeneracy on `K_R` gives

```text
p_K(z_i)=u_i.                                                  (PDS14)
```

Every `u_i` annihilates `S_sat`, hence every `z_i` annihilates the spherical
templates and belongs to `M_Sigma`.  Equation `(PDS14)` says precisely that
the map `u_i |-> z_i` splits `(PDS1)`.  End proof.

Using Theorem 1, `(PDS13)` is equivalent to the sparse conceptual system
`(PDS3)`: the packet columns prescribe the identity and the saturated
boundary columns prescribe zero.

## 4. Exact metric certificate

Put

```text
G_H=(<u_i,u_j>),       G_Z=(<z_i,z_j>).                       (PDS15)
```

The squared Euclidean norm of the constructed section is exactly the largest
generalized eigenvalue

```text
||s||^2=lambda_max(G_H^(-1)G_Z),                              (PDS16)
```

and its exact generalized characteristic polynomial is

```text
det(G_Z-t G_H).                                                (PDS17)
```

Subtracting any integral row of the range lattice `L` from a lift preserves
`(PDS13)`.  Therefore ordinary lattice reduction of the seven rows gives
certified decreasing upper bounds on `(PDS16)`; only a genuine CVP proof
would turn those upper bounds into optima.

Combined with Theorem 2 of
`TRUE_HARMONIC_RIESZ_PACKET_CRITERION.md`, a family of packet cycles and
packet-dual lifts with uniformly bounded Gram row sums would bound every
harmonic carry class simultaneously, even when harmonic rank grows.  The
present theorem constructs the exact finite object that must be bounded; it
does not yet prove that uniform family estimate.

## 5. Scope

This note closes a logical interface that was previously implicit:

```text
determinant-one primal packet
  -> integral splitting of the cycle lattice
  -> preferred basis of Q^#
  -> seven explicit ambient integer lifting problems
  -> exact dual carry section and section polynomial.         (PDS18)
```

It does **not** infer the dual section norm from the primal section norm.
That inference would be false without additional arithmetic control on the
embedding `K subset Lambda`; the size of the integral right inverse is
exactly the remaining numerator information.
