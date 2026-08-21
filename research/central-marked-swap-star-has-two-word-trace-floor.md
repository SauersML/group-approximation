---
rg: 2
id: central-marked-swap-star-has-two-word-trace-floor
kind: claim
title: A binary swap star confined to one central marked sector has a two-word canonical trace floor
distinct_from:
  even-partial-swap-star-has-canonical-trace-floor: that assumes the partial-swap chart controls the whole representation and lower-bounds the trace of one product word; this allows arbitrary action on the complementary central sector and cancels it with a second ordinary word.
  trace-cyclic-rank-mismatch-checksum: that uses cyclicity of two decoded products to compare projection ranks; this isolates one marked swap-star moment by the elementary central Fourier difference `h-yh`.
  dihedral-spin-packet-supplies-common-partial-swap: that supplies one common source in a central D8 spin sector; this gives the scalar checksum once two orthogonal ranges have been authenticated in that sector.
---

Let `Gamma` contain a central involution `y` and two involutions `j_0,j_1`.
Put

```text
p=(1-y)/2,                  h=j_0j_1.                 (MSS1)
```

Consider a finite-dimensional unitary representation and the normalized
trace `tau`.  Suppose that on the reducing subspace `pH`, after an arbitrary
unitary identification, the restrictions of `j_0,j_1` are a binary
partial-swap star: there are partial isometries `S_0,S_1` with

```text
S_i^*S_i=Q,
(S_0S_0^*)(S_1S_1^*)=0,                              (MSS2)
```

and `j_i|_(pH)=J_(S_i)` in the two-copy form of
`even-partial-swap-star-has-canonical-trace-floor`.  No condition is imposed
on `(1-p)H`.

Then

```text
Re tau(ph)>=1/4 tau(p),                               (MSS3)
```

and therefore

```text
Re(tau(h)-tau(yh))>=1/2 tau(p)
                    =1/4(1-tau(y)).                  (MSS4)
```

The estimate is dimension-free and invariant under spectator amplification.
It completely removes cancellation coming from uncontrolled one-dimensional
packet characters outside the marked sector.

## Nonhyperlinearity criterion

Assume the exact infinite witness has nonzero source `Q`.  On its marked
sector `h` contains a genuine three-cycle, so `h!=1`; because `y=-1` there,
`yh` is also nonidentity.  If `y` is nonidentity as well, canonical-trace
microstates satisfy

```text
tau(y)->0,             tau(h)->0,             tau(yh)->0. (MSS5)
```

If fixed packet exactification and the group relators recover `(MSS2)` with
`o(1)` normalized-Hilbert--Schmidt error on `pH`, word telescoping changes
`(MSS4)` by `o(1)`.  Its right side tends to `1/4`, whereas its left side
tends to zero by `(MSS5)`.  Hence no canonical hyperlinear microstate exists.

Thus a marked-sector compiler need not select the diagonal-complement signs
of either swap and need not prove a positive trace for `h` on the whole
matrix.  It needs only:

1. one central separated mark `y`;
2. a common-source, orthogonal-range binary star inside `p`;
3. exact nontriviality of the two words `h` and `yh`.

## Robust form

If the decoded restrictions differ from exact swaps by at most `epsilon`,
then

```text
Re tau(ph)>=1/4 tau(p)-2 epsilon.                     (MSS6)
```

The factor two is the length of `h=j_0j_1`; any fixed finite-packet rounding
error can be absorbed into `epsilon`.  No estimate on the complementary
sector appears.

## Attempts and firewalls

- **Lower-bound `tau(h)` directly.**  Uncontrolled finite-character sectors
  can contribute negative trace and cancel the star.  The central Fourier
  difference `h-yh` removes them exactly.
- **Use the group-algebra projection `p` as the final mark.**  Unnecessary:
  `(MSS4)` is the difference of the traces of two ordinary group words.
- **Claim the D8 packet already supplies two ranges.**  One D8 swap supplies
  one common source.  Orthogonalizing two ranges on the same marked source
  remains the load-bearing compiler step.
