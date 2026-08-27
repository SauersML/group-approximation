---
rg: 2
id: atlas-s576-carrier-completes-first-core-k22-proof
kind: route
title: Glue the S576 vertex to the canonical rank-three packet block
target: atlas-s576-carrier-completes-first-core-k22
requires:
  - atlas-s288-carrier-extends-through-first-core-cycle
  - atlas-a4-aligned-component-generation-ladder
---

Write the four labels of the first core rectangle as `r,u,b,y`, where `r,y`
have order three, `u,b` have order two, and

```text
u r u=r^-1,                 b y b=y^-1.                 (K22-1)
```

With the fixed packet alignment from
`atlas-a4-aligned-component-generation-ladder`, direct exact arithmetic in
`GL_4(F_2)` gives

```text
ord(r^-1 b)=ord(u y)=ord(u r y^-1)=ord(r b y)=3.        (K22-2)
```

Moreover

```text
<r,u> ~= S3,       <b,y> ~= S3,
<r,u,b> ~= S4,     <r,u,b,y> ~= GL3(F2),               (K22-3)
```

with respective orders `6,6,24,168`.  Thus the canonical rank-three block
closes all four edges, including the two edges not present at the preceding
S576 rung.

On the order-576 side, retain the notation of
`atlas-s288-carrier-extends-through-first-core-cycle`.  Its elements `r,u,b`
generate the same labeled `S4`, while the collision involution `c` commutes
with this subgroup.  Hence

```text
E=<r,u,b,c> ~= S4 x C2,             |E|=48.             (K22-4)
```

On the rank-three side adjoin a central collision involution, obtaining

```text
M=GL3(F2) x C2(c),                  |M|=336,             (K22-5)
```

with the same labeled subgroup `E`.  The regular restrictions match after the
smallest integral amplification:

```text
7 Reg(H_576)|_E = 7*12 Reg(E) =84 Reg(E),
12 Reg(M)|_E    =12*7 Reg(E)   =84 Reg(E).              (K22-6)
```

Both sides therefore act faithfully on `7*576=12*336=4032` points after a
permutation conjugacy aligning their `E`-actions.  The generated finite group
preserves the complete forward/collision carrier and all four edges of this
first rectangle.  The verifier checks every matrix word, subgroup order, and
multiplicity in `(K22-2)`--`(K22-6)` exactly.
