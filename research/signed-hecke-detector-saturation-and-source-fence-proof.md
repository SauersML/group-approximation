---
rg: 2
id: signed-hecke-detector-saturation-and-source-fence-proof
kind: route
title: Extract a root with two spare indices and audit which extractions must leave the signed source
target: signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped
requires:
  - paid-t00-carrier-has-signed-hecke-reynolds-dichotomy
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
  - signed-hecke-normalizer-has-eight-external-root-returns
---

Use the actor set

```text
A={2,4,5,6,7,8,9}
```

and two spare indices `p,k` outside `A union {1,3}`.  Every `g in L_0` is a
word in roots supported on `A`.  The commuting row roots

```text
X(v)=product_(j in A)x_(p,j)(v_j)                    (1)
```

form a right row module for the actor block.  This is an identity in the
Steinberg presentation: conjugating one factor in `(1)` by an actor root
uses one adjacent-root relation, and every other factor commutes.  The
displayed actor realization of `L_0` is faithful, so if `g!=1` there is a
basis row `e_i` for which

```text
[X(e_i),g]=X(v),                  v!=0.                (2)
```

Choose `j` with `v_j!=0`.  Since every other factor of `X(v)` commutes with
`x_(j,k)(1)`, a second Steinberg commutator isolates

```text
[X(v),x_(j,k)(1)]=x_(p,k)(v_j)!=1.                   (3)
```

The first commutator is a product of two conjugates of `g^(+/-1)` and the
second doubles that number.  Thus `(3)` is a product of at most four
conjugates of `g^(+/-1)`.  The reverse half of the uniform Leavitt root
sandwich writes `z` as a product of at most four conjugates of `(3)`, giving
the bound `16` in `(DSF2)` for every positive-character `g!=1`.

If `lambda_0(g)=-1`, then `r_g=zg`.  Choose instead one fixed root `h` on a
spare index which is adjacent to `z=x_13(q)` and disjoint from `A`.  The
actor-supported `g` commutes with `h`, while the Steinberg relation gives

```text
[r_g,h]=[z,h]=x_(1,k)(q)                             (4)
```

up to harmless orientation.  This is already a product of two conjugates of
`r_g^(+/-1)`, so the same root-to-mark sandwich gives the bound `8`.

The identity detector occurs exactly at `g=1`: on the positive half
`r_g=g`, while on the negative half the elementary image is block diagonal
with nontrivial `z` on `{1,3}` and `g` on the disjoint actor block.  Thus no
negative detector is trivial.  The faithful actor table similarly makes
every positive `g!=1` nontrivial.

For the other direction, every displayed generator of `L_0` is a nonzero
elementary root and hence, by the forward uniform sandwich, is a product of
four conjugates of `z`.  Every vertex of a connected Cayley graph on `8192`
vertices is reached by a simple path of length at most `8191`.  Substituting
the four-conjugate expression for each letter, and adding the possible
leading `z`, gives `(DSF3)`.

It remains to test whether `(2)--(3)` can be performed without leaving the
actual signed source normalizer.  The deterministic audit
`experiments/signed_hecke_detector_normal_closure_audit.py` reuses the
certified faithful binary table.  It splits the character fibers, forms
every conjugacy class in the `4095`-element nonidentity positive fiber,
closes each class normally in `L_0`, and tests intersection with all `13`
internal root transvections.  There are exactly `511` classes: `480` hit an
internal root in normal-word length at most two, while `31` miss every such
root.  Their `(class size, normal-closure size)` distribution is

```text
(1,2): 11 classes,       (2,4): 16 classes,
(4,8):  4 classes.                                      (5)
```

All arithmetic is exact over `F_2`; MSI job `17032181` used one CPU.

Finally, normal-word telescoping explains the analytic limit.  From `(DSF3)`,
largeness of `(r_g-1)C` forces one conjugate of `z` to be large on `C`, with
loss at most `32765`.  From `(DSF2)`, smallness of all conjugates of `r_g`
would force smallness of `z`.  Neither implication controls the image of
`C` under the conjugators.  For the `31` fenced positive classes the
conjugators cannot all lie in `L_0`, so the equality `gQ=lambda_0(g)Q` gives
no source preservation.  This is normal saturation, not a relator estimate
or a native selector occurrence.
