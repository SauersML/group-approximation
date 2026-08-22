---
rg: 2
id: expander-parity-checks-have-dense-clifford-shears
kind: claim
title: Positive-distance parity checks have exact dense named-site Clifford shears
distinct_from:
  lin-code-space-pauli-test-has-only-logarithmic-weyl-rank: that uses a vector in the orthogonal complement of a proper sampled code space; this uses a codeword in the kernel of a full parity-check family and therefore applies even when the checks define a good positive-distance expander code.
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that leaves an arbitrary simultaneous conjugacy after a globally rigid Pauli test; this exhibits a simultaneous conjugacy which fixes every parity-check observable and the entire transverse coordinate chart pointwise.
  adjoint-parity-defects-form-tanner-fundamental-cone: that spreads commutator magnitudes from exact parity; this gives a zero-defect coherent gauge and shows that classical distance or expansion cannot orient the named sites.
---

Let `H` be a binary parity-check matrix on `n` coordinates and

```text
C=ker(H) <= F_2^n.
```

Use the standard `n`-qubit Weyl packet, with Hermitian Paulis `X(a),Z(b)`.
For every nonzero `v in C`, put

```text
P=Z(v),                 W=exp(pi i P/4),
X_i'=W X_i W*,          Z_i'=Z_i.                         (EPCS1)
```

Then this is an exact Pauli packet and, more strongly,

```text
W Z(b) W*=Z(b)                         (b in F_2^n),
W X(h) W*=X(h)                         (h in rowspan(H)). (EPCS2)
```

Indeed `P` commutes with the whole `Z` chart.  It also commutes with `X(h)`
exactly when `v.h=0`, which holds for every check row because `Hv=0`.
Thus every parity-check word and every transverse coordinate observable is
fixed **pointwise**, not merely carried to a conjugate copy.  All Pauli
relations remain exact because `(EPCS1)` is simultaneous conjugation.

On the named coordinate frame this invisible gauge is maximally nonlocal.
For `i in supp(v)`, `P` anticommutes with `X_i`, so

```text
X_i'=i P X_i,                 ||X_i'-X_i||_2^2=2.          (EPCS3)
```

For `i notin supp(v)`, one has `X_i'=X_i`.  The norm identity follows from
Pauli orthogonality: `tau(X_i^* X_i')` is a phase times `tau(P)=0`.
Consequently, for every proposed bad-site set `B`,

```text
sum_(i notin B) ||X_i'-X_i||_2^2
   =2 |supp(v) minus B|.                                  (EPCS4)
```

If `C` has relative distance at least `Delta`, every nonzero invisible shear
therefore moves at least `Delta n` named sites by distance `sqrt(2)`, while
the complete parity-check defect is zero.  In particular an estimate of the
form

```text
zero (or o(1)) parity energy  =>  o(n) bad named sites      (EPCS5)
```

is false even for a good expander/LDPC code.  Positive distance makes the
smallest nontrivial invisible gauge *more* spatially extensive; it does not
turn coherent error into sparse adversarial noise.

This is deliberately a fixed-frame statement.  The global correction
`W*` removes the shear with no bad sites, so `(EPCS1)--(EPCS4)` do not refute
gauge-free Pauli exactification such as de la Salle's theorem.  They refute
the step needed by a fault-tolerant tape when the extracted packet must be
aligned with an already named computation frame.  Parity expansion alone
cannot provide that alignment.  A successful gadget must add incidence
whose commutant excludes every nontrivial `exp(pi i Z(v)/4)`, for example a
transverse generator-column anchor or a payload which is covariant under the
same global gauge.  Merely repeating or expanding the parity checks leaves
the exact kernel `(EPCS1)` untouched.

