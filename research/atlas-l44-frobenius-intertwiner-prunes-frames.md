---
rg: 2
id: atlas-l44-frobenius-intertwiner-prunes-frames
kind: claim
title: One Frobenius-twisted intertwiner line decides common L4(4) subfield descent
distinct_from:
  atlas-l44-h6-has-thirty-frobenius-frames: that counts the thirty H6-compatible subfield frames by centralizers; this gives a basis-free invariant for each frame and tests H18 compatibility without enumerating them.
  atlas-l44-local-packet-fans-do-not-force-subfield-support: that shows either local component alone has nonsubfield escapes; this is a simultaneous two-component descent criterion.
  atlas-l44-subfield-packet-collision-exclusion: that asks for the final packet/collision screen in L4(4); this removes the thirty-form inner loop but does not itself test collision 19243.
---

# One Frobenius-twisted intertwiner line decides common L4(4) subfield descent

ESTABLISHED. Let `k=F4`, let `V=k^4`, and write `V^(2)` for the Frobenius
twist. For a subgroup `J<=GL(V)` define

```text
T(J)=Hom_J(V^(2),V)
    ={D in M_4(k): D g^(2)=gD for every g in J}.        (L44I-1)
```

Assume the given four-dimensional representation is absolutely irreducible
(in particular `End_J(V)=k`). Then the following are equivalent.

1. `J` is contained in a conjugate of `GL4(2)`.
2. `T(J)!=0`.
3. The twisted tensor module

   ```text
   V tensor (V^(2))^*                                   (L44I-2)
   ```

   has a nonzero `J`-fixed vector.

Moreover, in this case `dim_k T(J)=1`, every nonzero `D in T(J)` is
invertible, and

```text
D D^(2)=I.                                              (L44I-3)
```

Thus the semilinear involution

```text
F_D(v)=D v^(2)                                          (L44I-4)
```

has a four-dimensional `F2` fixed space `V_D`, one has
`V=k tensor_(F2) V_D`, and `J<=GL(V_D)`. Multiplying `D` by an element of
`F4^*` changes the fixed vector space but not the associated subfield
subgroup, because the scalar cancels in `F_D g F_D^-1`. Hence the projective
line `[D]` is the exact invariant of the subfield frame.

The proof contains a dimension-four simplification useful for screening.
Any nonzero `D` is an isomorphism by irreducibility. The product
`N=D D^(2)` commutes with `J`, so `N=mu I`. Taking determinants gives

```text
mu=mu^4=det(N)=det(D) det(D)^(2)=1,                     (L44I-5)
```

because the norm of every nonzero element of `F4` is one. Thus no nonlinear
Hilbert-90 or norm equation remains after the linear intertwiner equations:
`(L44I-3)` is automatic.

Apply this to a marked candidate pair

```text
K'=image(H6),       L'=image(H18),       J=<K',L'>.     (L44I-6)
```

After checking absolute irreducibility (and hence the scalar commutant),
common subfield descent is decided by one linear system over `F4`:

```text
D k_i^(2)=k_iD,       D l_j^(2)=l_jD                    (L44I-7)
```

for any generating sets of `K'` and `L'`. A zero solution space rejects the
pair. A nonzero solution gives the unique projective common form and a basis
of `V_D`; conjugating by that basis reduces all subsequent packet and
collision tests to `GL4(2)`. There is no `30 x 6` Frobenius-form loop after
the simultaneous `H18` placement is known.

For the thirty forms containing the fixed standard `K=H6`, the invariant is
especially concrete. Each is represented by a projective norm-one element

```text
[D] in P(T(K))=P(End_K(V)),                             (L44I-8)
```

and the thirty distinct subfield frames are exactly the thirty projective
classes arising as `D=c(c^(2))^-1` for `c in C_G(K)`. Compatibility with a
candidate `L'` is precisely the additional linear equations in `(L44I-7)`.
This classifies the forms by an exact invariant rather than by a chosen list
of centralizer representatives.

There is also a minimal conjugator version. Since the certified standard
`K,L` generate `A=GL4(2)`, a matrix `c in GL4(4)` lies in
`F4^* GL4(2)` exactly when the conjugates of generators of both `K` and `L`
are entrywise Frobenius-fixed. Indeed those equations imply

```text
c^-1 c^(2) in C_G(<K,L>)=F4^*,                         (L44I-9)
```

so `c^(2)=lambda c`; every nonzero entry of `c` is then the same scalar
multiple of an `F2` entry. This is the smallest relation-sensitive descent
certificate once both packet components share one conjugator.

The theorem does not prune a merely `H6`-marked fiber: its five-dimensional
twisted commutant genuinely contains all thirty classes. Its gain begins
exactly where the current endpoint computation becomes expensive—when one
candidate `H18` placement must use the same frame.
