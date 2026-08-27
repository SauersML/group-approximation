---
rg: 2
id: mf-equivalences-form-a-colimit-stable-localization
kind: claim
title: MF-equivalences form a colimit-stable reflective localization of countable groups
artifacts:
  - research/mf-equivalences-form-a-colimit-stable-localization-proof.md
---

Call a homomorphism `f:G->H` an **MF-equivalence** when

```text
R_MF(f):R_MF(G)->R_MF(H)
```

is an isomorphism.  Equivalently, pullback along `f` is a natural bijection

```text
Hom(H,M) ~= Hom(G,M)                                  (ME1)
```

for every countable MF group `M`.

Then:

1. MF-equivalences contain all isomorphisms, satisfy two-out-of-three, and
   are closed under retracts;
2. every countable colimit of a natural transformation which is objectwise
   an MF-equivalence is again an MF-equivalence;
3. in particular they are stable under pushout, countable sequential
   composition, and arbitrary countable presentation gluing;
4. a surjection `f:G->H` is an MF-equivalence exactly when
   `ker(f)<=Rad_MF(G)`;
5. the category of countable MF groups is the reflective localization of
   countable groups obtained by inverting all MF-equivalences.

Consequently, if `A` has full MF radical, the map `A->1` may be substituted
inside any countable group colimit without changing the final MF reflection.
For any map `A->G`, its pushout gives

```text
G -> G/normalClosure(image(A)),
```

and this quotient is automatically an MF-equivalence.  The same remains true
after any countable network of further pushouts, amalgams, HNN extensions,
and directed unions.
