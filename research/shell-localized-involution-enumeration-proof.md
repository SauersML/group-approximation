---
rg: 2
id: shell-localized-involution-enumeration-proof
kind: route
title: Recover every shell index by enumerating equalities between conjugates of localized prefix flips
target: shell-recursive-presentations-compute-enumerations
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

Let v_n be the involution that interchanges 0^n*1*0*C and
0^n*1*1*C by prefix replacement and fixes their complement. Its
support is exactly the shell C_n. The v_n are nonidentity and
pairwise distinct.

The three prefix elements to mark are v_0, v_1, and t, whose table is

    0*z  -> 00*z,
    10*z -> 01*z,
    11*z -> 1*z.

This is a binary prefix homeomorphism fixing p=0^infinity. It maps
C_n to C_(n+1) by pure prefix replacement whenever n>=1. Hence

    v_n=t^(n-1)*v_1*t^(-(n-1))       for n>=1.

All the v_n are thus given effectively as words in these three
elements. They and t belong to A_1 as well as E_nu. So do the
finitely many hat(g), g in S.

Because a shell generator preserves the entire suffix in each shell,

    hat(g)*v_n*hat(g)^-1 = v_(rho_g(n)).

The same formula holds for a word g in S. From a correct recursive
presentation with the listed marked words, enumerate consequences
of the relators. For given g,n, dovetail over m>=0 and proofs of

    hat(g)*v_n*hat(g)^-1*v_m^-1 = 1.

Exactly one m satisfies this equality, and its proof is eventually
enumerated. The search therefore halts and returns rho_g(n).
It requires enumeration of true equalities, not a word-problem
oracle for the shell group. No computability of nu was assumed.

The even-index action is free and regular. Thus g=1 in P exactly
when rho_g(0)=0, which decides the word problem of P. If the fixed
integer n_0=nu(1_P) is supplied, then

    nu(g)=rho_g(2*n_0)/2.

This computes nu on S-words. For a requested index j, enumerate
S-words w and their computed nu(w) until nu(w)=j; surjectivity
ensures termination, giving an inverse word representative.

If a recursive presentation is given on a different generating set,
the finitely many marked elements still have words in that set.
Fix those words, and fix n_0, as finite constants. This proves the
nonuniform existence assertion for any abstract recursive presentation.
It does not make correctness of the marked presentation decidable.

For the countability assertion, fix a countable abstract group Gamma.
There are only countably many tuples in Gamma marking hat(S),t,v_0,v_1,
and only countably many possible integers n_0. The conjugacy equalities
above uniquely determine rho and then nu from any tuple actually
arising from an isomorphism with a shell group. This uniqueness argument
does not require Gamma to have a recursive presentation or computable
operations. Thus a fixed Gamma accounts for at most countably many
enumerations. There are continuum many bijections P->N, and all the
groups in either family are countable. Dividing a continuum-sized set
into countable isomorphism fibers gives continuum many isomorphism
classes, as claimed.
