# A literal fixed-word fiber mixer would already solve the exact packet

Date: 2026-08-14

## Outcome

The conditional-variance and fixed-library endpoints do not combine through
an exact action of a fixed family of group words on the extension characters.
Such an action would make the desired measurability true already in the
regular representation, contradicting the exact Pauli packet.

This closes the following tempting search:

```text
find fixed words preserving the raw branch statistic
  + make those words mix every comb extension fiber
  + apply a Reynolds/spectral-gap estimate.
```

The missing mixer, if it exists, must instead be recovered from the
finite-coordinate multiplicity algebra. It cannot be a literal action on the
canonical packet which is visible in every representation.

## 1. The finite-set lemma

Let `pi:X->Y` be a map of finite sets and let a group `K` act on `X`. Assume
that the action is transitive inside every fiber:

```text
pi(x)=pi(x')  =>  there is k in K with kx=x'.          (LFM1)
```

If a label `r:X->A` is `K`-invariant, then

```text
pi(x)=pi(x')  =>  r(x)=r(x').                         (LFM2)
```

Indeed, choose `k` as in `(LFM1)` and compute
`r(x)=r(kx)=r(x')`. Thus `r` factors through `pi` on every nonempty fiber.

This implication is formalized source-first as
`KazhdanFiniteModel.invariant_label_eq_of_same_fiber` in
`GroupApproximation/Kazhdan/KazhdanFiniteModel.lean`. No build was run.

## 2. Reynolds form

Let `(E_x)_(x in X)` be a finite PVM and put

```text
F_y=sum_(pi(x)=y) E_x,
B=sum_(r(x)=1) E_x,
A_Y=W*(F_y:y in Y).                                  (LFM3)
```

Suppose unitaries `(U_k)_(k in K)` permute the atoms according to the action.
If the `K`-orbits are exactly the fibers of `pi`, then conjugation averaging
over `K`, restricted to the diagonal atom algebra, is precisely the
trace-preserving conditional expectation onto `A_Y`. Consequently

```text
(1/|K|) sum_k ||[U_k,B]||_2^2
  =2 ||B-E_(A_Y)(B)||_2^2.                            (LFM4)
```

Equation `(LFM4)` is the finite-group mean-displacement identity already
formalized in `PropertyT/FiniteGroupAverage.lean`, together with the orbit
description above. In particular, exact commutation of `B` with every `U_k`
forces

```text
B=E_(A_Y)(B) in A_Y.                                 (LFM5)
```

A generating-set version replaces the average over `K` by a uniform spectral
gap on the fiberwise centered diagonal subspace. It has the same zero-energy
consequence: an invariant label is fiber-constant.

## 3. Conflict with the exact atlas packet

For the canonical Pauli carrier, write

```text
E=PQ,                     F=U*QU,
tau(E)=1/8,               tau(F)=1/4,
tau(EF)=1/32.                                      (LFM6)
```

The exact packet calculation gives

```text
E_(W*(E))(F)=(1/4)1,
||F-E_(W*(E))(F)||_2^2=3/16.                          (LFM7)
```

More generally, the raw binary router is not known to be constant on the
comb extension-character fibers; proving that constancy is exactly the live
decoder gate.

Now suppose fixed literal words supplied an exact fiber action and their
printed group relations made the relevant branch statistic invariant. Those
same word identities hold in the left regular representation. Applying
`(LFM2)` or `(LFM5)` there would put the branch statistic in the coarse fiber
algebra. In the Pauli specialization this contradicts `(LFM7)`.

Therefore there is no hidden exact fixed-word fiber mixer inside the current
packet. Adding more literal words and checking that they preserve the branch
cannot produce transitivity on the required fibers.

## 4. What remains live

This does **not** rule out a matrix-specific fiber action. A finite-coordinate
recovery theorem may produce atom permutations or commutant symmetries which
depend on the coordinate and have no literal counterpart in the regular
representation. Such emergent symmetries could mix the multiplicity fibers
and turn the conditional variance into commutator energy.

The distinction is now sharp:

```text
literal fixed-word action on canonical atoms             impossible;
coordinate-dependent action recovered from multiplicity  still live.
```

Accordingly the next proof cannot be only another word search. It must first
recover finite multiplicity coordinates (or an equivalent whole-map PVM)
from the normalized-Hilbert--Schmidt microstate. Once that recovery exists,
`(LFM4)` and the binary majority decoder turn its fiber mixing into the
already certified `3/16` Pauli contradiction or the robust paired-quotient
floor.
