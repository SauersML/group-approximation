---
rg: 2
id: atlas-q14-index-32-prime-power-exclusion-proof
kind: route
title: Apply the finite-simple prime-power-index classification at degree thirty-two
target: atlas-q14-simple-overgroup-index-is-at-least-33
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-32
---

The preceding sieve gives `n=[S:A]>=32`, where `S` is nonabelian simple and
`A ~= A8`.  Suppose `n=32=2^5`.

Guralnick's classification of subgroups of prime-power index in finite
nonabelian simple groups says that a proper subgroup `H<S` of index `p^a`
occurs only in the following cases.

```text
(G1) S=Alt(m), H=Alt(m-1), and m=p^a;
(G2) S=PSL_d(q), H is a line or hyperplane stabilizer, and
     (q^d-1)/(q-1)=p^a;
(G3) (S,H)=(PSL_2(11),A5);
(G4) (S,H)=(M11,M10) or (M23,M22);
(G5) S=PSU_4(2) ~= PSp_4(3), with H parabolic of index 27.
```

Apply this with `H=A ~= A8` and index 32.  Case `(G1)` would give
`(S,H)=(A32,A31)`, so it does not have `H ~= A8`.  The exceptional indices
in `(G3)`--`(G5)` are respectively 11, 11, 23, and 27, never 32.

It remains to solve the projective index equation

```text
1+q+...+q^(d-1)=32,                                  (OSI33-3)
```

where the classification permits `d` prime.  For `d=2`, the unique solution
is `q=31`; the line stabilizer in `PSL_2(31)` has order

```text
31(31-1)/gcd(2,30)=465,
```

not `|A8|=20160`.  For `d>=3`, monotonicity reduces the check to the first
prime dimensions.  At `d=3`, `q^2+q+1` jumps from 31 at `q=5` to 43 at
`q=6`; hence it is not 32.  At `d=5`, its minimum is 31 at `q=2`, and every
larger prime power gives a value greater than 32.  For `d>=7`, even `q=2`
gives at least 127.  Thus `(G2)` also has no subgroup isomorphic to `A8` at
index 32.

All classified cases are impossible.  Therefore `n!=32`; combined with the
preceding lower bound, `n>=33`.  Since the argument excludes the ambient
degree before inspecting `A intersect B`, it simultaneously removes the
`A7`, `2^3:GL_3(2)`, and `S6` intersection profiles.

