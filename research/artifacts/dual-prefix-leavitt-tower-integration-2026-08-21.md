---
rg: 2
id: dual-prefix-leavitt-tower-integration-2026-08-21
kind: artifact
title: Deduplication map for the universal W/W-star dual-prefix Leavitt tower
---

# Translation of the universal operator notation

The universal `W/W^*` picture consists of two isometries on an infinite
active carrier,

```text
W_i^*W_j=delta_(i,j)I,          sum_i W_iW_i^*=I.       (WW1)
```

It is exactly the represented form of the already used relative Leavitt
relations, under

```text
s_i -> W_i,             t_i -> W_i^*.                  (WW2)
```

For a binary word `u`, the report's forward prefix `x_u` is `s_u=W_u` and
its dual `y_u` is `t_u=W_u^*`, with the reversal convention in
`iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart`.  Hence

```text
y_u x_v=t_u s_v=delta_(u,v)A                            (WW3)
```

and `x_u y_v=s_ut_v` are the depth-`n` matrix units.  This exact algebra is
not duplicated in a new tower node: `(WW3)` feeds the existing
`leavitt-prefixes-form-exponential-heisenberg-packet`.

# Existing Cairn destinations

- Exact `y_u x_v` pairing and the full `Phi_n` chart:
  `iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart`.
- Common-sign Pauli/Heisenberg tower and marked-sector divisibility
  `p^(2^n)`: `leavitt-prefixes-form-exponential-heisenberg-packet`.
- Exact annihilation of the active mark in every finite-dimensional
  representation: `affine-leavitt-steinberg-mark-is-fd-invisible`.
- Prefix-cost distinction: `leavitt-steinberg-quadratic-radius-pressure`
  now separates address length, balanced root-word length, and equality-table
  van Kampen area.
- Exact first-step `s4` endpoint:
  `four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap`.
- Remaining common-corner/multiplicity target:
  `paired-same-reservoir-boundary-lemma` and
  `common-corner-mutual-bicommutant-extraction`.

# Positive diagonal-density tradeoff

There are two distinct finite-matrix consequences, and confusing them is the
main danger in the universal notation.

First, an exact unital realization of `(WW1)` in a finite tracial corner is
impossible.  If its active identity is `P`, cyclicity would give

```text
tau(W_iW_i^*)=tau(W_i^*W_i)=tau(P),
tau(P)=sum_i tau(W_iW_i^*)=2tau(P),                    (WW4)
```

so `tau(P)=0`.  The robust version is already
`approximate-relative-leavitt-cell-kills-active-trace`:

```text
tau(P)<=||T_0S_0-P||_2+||T_1S_1-P||_2
       +||S_0T_0+S_1T_1-P||_2.                        (WW5)
```

Second, a finite **depth-n matrix-unit chart** is perfectly possible.  Its
`2^n` diagonal prefix projections are Murray--von Neumann equivalent,
orthogonal, and sum to `P`; therefore

```text
tau(s_ut_u)=2^(-n)tau(P)       for every |u|=n.         (WW6)
```

Thus a single named diagonal prefix loses density exponentially even while
the total marked sector remains macroscopic.  One must either aggregate the
whole depth (which yields only the existing dimension-divisibility pressure)
or return the refined packet to the **same** positive-density source
reservoir.  The latter is precisely the open same-corner theorem.  At depth
one and `p=2`, once the same four returned words are both source-confined and
target-Pauli, the existing `s4` estimate gives

```text
144 epsilon+96 delta>=8.                                (WW7)
```

The exact infinite `W/W^*` model supplies completeness, `(WW5)` supplies the
finite-trace annihilation after coefficient decoding, and `(WW6)--(WW7)`
locate the only remaining groupification gap.  No additional exact Pauli
algebra or polynomial identity is missing.

