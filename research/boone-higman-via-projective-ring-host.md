---
rg: 2
id: boone-higman-via-projective-ring-host
kind: route
title: Embed the simple core as elementary diagonal matrices and pass to a finitely presented simple projective host
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, clapham-fp-embedding-preserves-word-problem, decidable-group-ring-has-fp-projective-simple-host]
artifacts:
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
---

Given a finitely generated group G with solvable word problem, apply the
Boone--Higman--Thompson theorem to G x Z to embed G in an infinite,
finitely generated, computably presented simple group S. Its word
problem is decidable: equality follows by enumerating relator consequences,
and inequality by enumerating witnesses that a fixed nonidentity word lies
in the normal closure of the tested word. Simplicity makes the second
search halt exactly when the tested word is nonidentity. Clapham therefore
supplies a finitely presented group H with solvable word problem containing S.

Apply the open projective-host hypothesis to H. The canonical group
embedding S -> L^x induces the injective diagonal homomorphism
d(s)=diag(s,1,1,1). Its image lies in EL_4(L), as follows.

An infinite simple group is nonabelian and perfect. For units a,b, put
A=diag(a,a^-1,1,1) and B=diag(b,1,b^-1,1). Each is elementary: on its
two active coordinates the identity

    (e_ij(u)e_ji(-u^-1)e_ij(u))
    (e_ij(-1)e_ji(1)e_ij(-1)) = diag(u,u^-1)

expresses it as a product of elementary matrices. Matrix multiplication
then gives [A,B]=diag([a,b],1,1,1). Since every element of the perfect
group S is a finite product of commutators, every d(s) is elementary.

The map remains injective after quotienting by Z(EL_4(L)). If d(s) is
central, it commutes with every d(t), so s in Z(S)=1. Hence

    G <= S <= PEL_4(L).

The final group is finitely presented and simple by the explicitly open
host hypothesis. This proves the conditional route, without assuming that
ring simplicity implies group simplicity or that the center is finitely
generated. No sandwich extension, and no decidability claim for one, is
needed in this reduction.
