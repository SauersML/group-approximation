# Exact local quantum recovery for a split cellular map

Research audit dated **2026-09-12**. The construction uses the classical
[Bennett-style reversible compute/uncompute method](https://www.cs.princeton.edu/courses/archive/fall04/cos576/papers/bennett73.html) and the quasilocal
compression setup of the
[2026-09-07 audit](gottschalk-quantum-compression-2026-09-07.md).
No external priority claim is made for the recovery construction.

This audit proves that the reversible-dilation approach really does supply
completely positive recovery on all quantum coherences. It does not prove
surjunctivity. In particular, recovery is not being substituted for
multiplicativity, trace preservation, or normality in a prescribed von
Neumann representation.

## 1. Statement

Let `G` be a group, let `A` be an alphabet of size `d`, and let

```text
F,D : A^G -> A^G,                 D F = id
```

be cellular maps. Identify `A` with the cyclic group `Z/d`. For a finite
set `S`, let `Q(S)` be the full matrix algebra on the spins in `S`, and
write `Q_G` for the norm closure of their union. Suppose memories `M,N`
for `F,D`, respectively, contain the identity; an output at `g` reads
`gM` or `gN`.

There are unital completely positive maps

```text
phi,psi : Q_G -> Q_G,             phi psi = id,             (1)
```

which commute with translations and have finite locality bounds. One
possible choice obeys

```text
phi(Q(S)) subset Q(S N^{-1}N M^{-1}M),
psi(Q(S)) subset Q(S M^{-1}M N^{-1}N).                       (2)
```

Here `phi` is the Heisenberg map of encoding by `F`, and `psi` is the
Heisenberg map of its quantum recovery channel. On diagonal observables,

```text
phi(f)=f composed with F,          psi(f)=f composed with D. (3)
```

The corresponding Schrödinger channels satisfy `Recovery Encoding=id`
on the entire state space of `Q_G`, not only on diagonal states.

## 2. Two reversible circuits

First normalize the constant configurations. If `F(0)=c`, replace `F`
by `F-c` and `D(y)` by `D(y+c)`. These maps still satisfy `DF=id` and
now fix zero. This is conjugation by an onsite permutation at the output
and does not change any locality bound or surjectivity question. Reverse
this normalization at the end if necessary.

On a physical and an ancillary copy of `A^G`, define

```text
T_F(x,a)=(x,a+F(x)),
S_D(x,a)=(x-D(a),a),
R_F,D = swap composed with S_D composed with T_F.
```

Each shear is a reversible cellular map. Their composite is

```text
R_F,D(x,a)=(a+F(x), x-D(a+F(x))).                           (4)
```

Consequently

```text
R_F,D(x,0)=(F(x),0).                                       (5)
```

Interchange `F,D` to obtain the recovery circuit:

```text
R_D,F(y,0)=(D(y), y-F(D(y))).                              (6)
```

For `y=F(x)`, equation (6) gives `(x,0)`.

These are finite circuits of commuting controlled-add gates, followed by
an onsite swap. For `T_F`, the gate at `g` reads physical spins `gM`
and adds the resulting alphabet value to ancillary spin `g`. Distinct
gates commute: they have distinct target registers, and every control is
in the opposite, unmodified register. The analogous statement holds for
`S_D`. No coloring of the Cayley graph and no amenability assumption is
required.

## 3. Quantum locality

Quantize each finite controlled permutation by its permutation matrix.
The commuting family defines an automorphism of the quasilocal algebra:
when conjugating an observable of finite support, only finitely many
gates fail to commute with it. Since the gates commute with each other,
the remaining gates cancel from the conjugation, including gates whose
supports meet the newly enlarged support.

More explicitly, for a shear with memory `M`, every gate affecting an
observable supported on a set `S` has its target in `S M^{-1}` or in
`S`. Its complete support is contained in `S M^{-1}M`, because the
identity belongs to `M`. This bound holds for the shear and its inverse.
The swap preserves support. Thus Heisenberg conjugation for (4), read
backwards through the circuit, expands `S` first by `N^{-1}N`, then by
`M^{-1}M`. The reversed circuit gives the other bound in (2).

Let `omega_0` be the product state with every ancillary spin in basis
state zero. If `alpha_F,D(O)=U_F,D^* O U_F,D` denotes the Heisenberg
automorphism just constructed, set

```text
phi(O)=(id tensor omega_0)(alpha_F,D(O tensor 1)),
psi(O)=(id tensor omega_0)(alpha_D,F(O tensor 1)).           (7)
```

The slice map in (7) is unital completely positive and does not increase
support. Equations (2) and translation covariance follow. Formula (3)
follows directly from (5) and (6).

## 4. Recovery of off-diagonal matrix elements

Here is a representation-level verification of (1) which avoids an
undefined infinite partial trace. Let `H_0` have the orthonormal basis of
configurations differing from zero at finitely many sites. The quasilocal
spin algebra acts faithfully on `H_0`: each finite matrix algebra acts
faithfully and isometrically, so their norm-dense union does also.

Since the normalized cellular maps fix zero and have finite memories,
the two reversible circuits act as permutation unitaries on
`H_0 tensor H_0`. Their initialized isometries are

```text
V_E |x> = |F(x)> tensor |0>,
V_R |y> = |D(y)> tensor |y-F(D(y))>.                       (8)
```

Use a fresh ancilla for recovery. On every finite configuration,

```text
(V_R tensor id) V_E |x> = |x> tensor |0> tensor |0>.       (9)
```

Equation (9) holds as an equality of isometries, by linearity and norm
continuity. Compressing `O tensor 1 tensor 1` by the two sides gives
`phi(psi(O))=O` for every local observable, including every off-diagonal
matrix unit. Faithfulness and norm continuity prove (1) in `Q_G`.
Dualizing proves the assertion about all states, without restricting to
normal states in this particular faithful representation.

For uncountable groups, the same finite-support construction works with
the corresponding possibly nonseparable Hilbert spaces. No exhaustion by
a countable sequence is needed.

## 5. What completely positive recovery actually implies

For any UCP maps satisfying (1), Schwarz inequalities give

```text
psi(a)^* psi(a) <= psi(a^*a),
a^*a <= phi(psi(a)^*psi(a)) <= phi(psi(a^*a))=a^*a.
```

The same argument applies to `aa^*`. Hence every `psi(a)` belongs to
the multiplicative domain of `phi`. In particular, `phi` restricts to
a surjective star homomorphism

```text
C^*(psi(Q_G)) -> Q_G.                                     (10)
```

This does not show that `psi` is multiplicative. It shows only that
`phi` annihilates its positive multiplicative defects. If `phi` were
faithful on positive elements, those defects would vanish, but that
faithfulness is not supplied by (1).

Indeed, if `F(A^G)` is proper, a nonempty cylinder disjoint from the
image has a nonzero diagonal characteristic projection `e`, while
`phi(e)=0` by (3). The earlier
[quantum-compression audit](gottschalk-quantum-compression-2026-09-07.md)
also constructs a local unitary with multiplicative defect of norm one
for this encoding map. Exact quantum recovery and that defect are
therefore compatible.

## 6. A finite-factor shortcut that does not work

For an infinite countable group and `d>=2`, one might represent the
physical spins in their product trace and the
ancillas in their pure zero state, obtaining

```text
M=R tensor B(H_0),
```

where `R` is the physical tracial factor. The all-zero ancillary
projection has semifinite trace one. A quasilocal automorphism need not
extend normally to this prescribed representation, so preservation of
its finite trace cannot be assumed for an infinite product of transformed
ancillary projections.

Nor does translation invariance exclude a physical factor of type
`II_infinity`. For an onsite alphabet `B times B`, take the product trace
on the first track and the pure zero state on the second. Its GNS factor
is exactly `R_B tensor B(H_0)`, and its finite-trace vacuum projection is
translation invariant and noncentral. Thus a purported argument that all
translation-invariant semifinite factor states on a spin algebra must
be tracial is false.

In fact, for this specific shear automorphism, normal extension to `M`
is equivalent to surjectivity of `F`. To see the forward implication,
write `omega=tau tensor omega_0`. A normal extension makes
`omega composed with alpha_F,D` normal on `M`. Its physical diagonal
marginal is `F_* nu`, where `nu` is uniform Bernoulli measure. Thus
`F_*nu` must be absolutely continuous with respect to `nu`.

If the closed invariant image `Y=F(A^G)` is proper, choose a nonempty
finite cylinder disjoint from it. There are infinitely many translates
of this cylinder having pairwise disjoint coordinate supports: choose
them successively, avoiding finitely many group elements at each step.
The corresponding independent Bernoulli events have the same positive
probability. Every point of `Y` avoids all of them, so `nu(Y)=0`, while
`F_*nu(Y)=1`. This contradicts absolute continuity. No assumption about
the scaling of the semifinite trace is necessary for this argument.

Conversely, if `F` is onto, `D` is its cellular inverse. Encoding then
induces an automorphism of the physical spin algebra, which preserves
its unique trace. The output ancilla is exactly pure zero by (5), so
`omega composed with alpha_F,D=omega`. The GNS unitary for this
state-preserving automorphism supplies its normal extension to `M`.

Equal onsite dimension, covariance, and locality remain available
constraints in (1). No index, finite-capacity inequality, or automatic
normality theorem deriving surjectivity from those constraints is proved
here. The normality equivalence identifies the missing assertion rather
than providing it.
