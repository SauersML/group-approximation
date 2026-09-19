---
rg: 2
id: heisenberg-subgroup-cuts-affine-proof
kind: route
title: Fourier-expand a Pauli stabilizer projector and read off its affine atom support
target: heisenberg-subgroup-cuts-are-affine-stabilizer-flats
requires:
  - canonical-finite-packet-data-stop-at-scalar-overlaps
---

Write the commutator relation in `E` as

```text
[x,y]=J^<xbar,ybar>,
```

where the induced alternating form on `V` is nondegenerate.  Suppose the
space `(HSC1)` contains `0 != xi`.  If `a,b in A`, then both act scalarly on
`xi`, and therefore their commutator fixes `xi`.  Since `pi(J)=-I`, one
cannot have `[a,b]=J`.  Thus `<abar,bbar>=0` for every `a,b in A`, proving
that `W=A<J>/<J>` is isotropic.  Compatibility with `J` is the only remaining
condition on `chi`; an incompatible character gives the zero cut.

Choose lifts of a basis of `W`.  Their commuting images have the prescribed
joint-character projector

```text
p=2^(-r) sum_(w in W) conjugate(chi(w)) pi(w).           (HSP1)
```

Every noncentral Pauli has trace zero: for `0 != w in V`, nondegeneracy
provides `v` with `<v,w>=1`, and conjugation by `pi(v)` changes `pi(w)` to
`-pi(w)`.  Cyclicity of trace then gives `Tr(pi(w))=-Tr(pi(w))`.  Taking the
trace in `(HSP1)` leaves only the identity coefficient, so

```text
Tr(p)=2^n/2^r=2^(n-r).                                  (HSP2)
```

Since `(HSP1)` is the ordinary average of commuting character projections,
it is the orthogonal projection onto `(HSC1)`.  This proves `(HSC2)` and
`(HSC3)`.

The `4^n` Pauli operators form an orthogonal basis of `M_(2^n)(C)` for the
Hilbert--Schmidt inner product: the product of two distinct Paulis is a
noncentral Pauli up to phase and hence has trace zero.  Fourier support in
`(HSP1)` is therefore unique.  Equality of two nonzero subgroup-character
cuts forces equality of their supports `W` and then equality of every
character coefficient.

Finally fix a maximal isotropic `L`.  Its minimal joint eigenspaces are the
one-dimensional atoms `p_lambda`, `lambda in L^*`.  Fourier inversion gives

```text
sum_(lambda in S) p_lambda
 = |L|^(-1) sum_(w in L)
     (sum_(lambda in S) conjugate(lambda(w))) pi(w).     (HSP3)
```

If `S=lambda_0+W^perp`, the inner sum vanishes off `W` and equals
`|W^perp| conjugate(lambda_0(w))` on `W`, so `(HSP3)` is `(HSP1)`.
Conversely, if `(HSP3)` equals `(HSP1)`, its range is the set of joint
characters extending the prescribed character on `W`, namely exactly the
affine flat `lambda_0+W^perp`.  This proves the classification and all three
stated consequences.
