---
rg: 2
id: free-product-bijective-base-shell-proof
kind: route
title: Encode alternating normal forms with their first syllable as the least significant bijective-base digit
target: a5-free-product-has-simple-arithmetic-shell-envelope
requires:
  - arithmetic-shell-envelopes-have-decidable-word-problem
  - perfect-input-shell-envelopes-are-simple
  - rational-shell-permutations-are-eventually-periodic
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

The arithmetic construction works for P=F*F with F any finite
group of order h+1, h>=2. Assign digits 1,...,h to its nonidentity
elements. Every positive integer q has a unique finite bijective-base-h
expansion q=d_1+h*d_2+... with digits 1,...,h: extract
d_1=1+((q-1) mod h) and replace q by (q-d_1)/h until zero.
At each nonterminal step q strictly decreases.

A nonempty reduced free-product word is uniquely specified by
its first factor type epsilon and the sequence of nonidentity
syllables, with the factor types then alternating. Therefore
nu(word)=2*q-1+epsilon bijects these words with the positive
integers; adding nu(1)=0 proves the required bijection.

## Exact generator formulas

Let a!=1 belong to factor i in {0,1}, with digit A. For input n=0,
left multiplication has output 2*A-1+i. For n>=1 recover

    epsilon=(n+1) mod 2,
    q=(n+1-epsilon)/2,
    d=1+((q-1) mod h),
    r=(q-d)/h.

Let a_d be the factor element labeled by d. There are three cases:

1. If epsilon!=i, prepend a. The new q is A+h*q, the type is i,
   and the new index is 2*(A+h*q)-1+i.
2. If epsilon=i and c=a*a_d!=1, combine the first syllable.
   The new q is digit(c)+h*r, with the same type i.
3. If epsilon=i and a*a_d=1, remove the first syllable. If r=0
   the result is the identity, index 0. Otherwise its new type is
   1-i, new q is r, and new index is 2*r-i.

These are precisely the normal-form rules for multiplication in F*F,
so they define the transported regular action. Inverses use the same
rules with a^-1. Away from finitely many single-syllable exceptions,
the cases are determined by n modulo 2h. The slopes are respectively
h, 1, and 1/h. Thus the formulas are affine on residue classes,
and passing to even shell indices and fixing odds gives the same
kind of finite arithmetic data, with a refined modulus.

## The A5 benchmark and its limits

Set F=A_5 and h=59. The group P is infinite, finitely presented,
and perfect: its finite factors are perfect and generate it. The
shell realization embeds it faithfully and gives a finitely generated
E_nu. The perfect-input simplicity claim makes E_nu simple, and
the arithmetic word-problem claim makes it decidable and recursively
presented.

For every nonidentity factor element a, case 1 occurs on an infinite
set of inputs and has slope 59. Its displacement from the original
index is unbounded; doubling to even shell indices preserves that
fact. The rational-shell characterization therefore excludes a
finite-state deterministic transducer for hat(a). This does not
conflict with the finite arithmetic formulas: an algorithm storing
an unbounded integer q is a different computational model.

The proof supplies the entire action and a word-problem algorithm,
but no finite set of defining relations for E_nu. That final
presentation problem is retained as a separate open benchmark.
