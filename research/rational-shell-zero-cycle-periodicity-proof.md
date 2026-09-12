---
rg: 2
id: rational-shell-zero-cycle-periodicity-proof
kind: route
title: Follow the unique all-zero state cycle and use bijectivity to force its output rate to be one
target: rational-shell-permutations-are-eventually-periodic
requires: []
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

Suppose a deterministic asynchronous transducer with finitely many
states realizes h_pi. On the input 0^infinity, every output symbol
is zero, since h_pi fixes p. After a finite prefix, the states
visited on successive zeros enter a cycle of some length m>=1.
Let a be the number of output zeros produced on one traversal.
We have a>=1: otherwise this input would produce only finitely
many output symbols, contrary to defining a Cantor homeomorphism.

For every sufficiently large n, the states after reading 0^n and
0^(n+m) coincide, and the latter accumulated output is the former
with a extra zeros. Feeding the same remaining input 1*z gives

    0^(pi(n+m))*1*z = 0^(pi(n)+a)*1*z.

Thus pi(n+m)=pi(n)+a eventually. Each of the m source residue
rays is mapped, after finitely many exceptions, to an arithmetic
progression of step a. Their target residues modulo a are distinct:
otherwise two image tails would overlap, contradicting injectivity.
They exhaust the a target residues by surjectivity. Therefore a=m.
This proves the required eventual periodicity. The key restriction
is the unique state cycle on all-zero input; the transducer cannot
wait to learn the final residue before choosing a different output
rate along that same arbitrarily long input prefix.

Conversely assume the displayed eventual periodicity. Then pi(n)-n
is bounded, since it is periodic outside a finite initial interval.
Choose an integer D>=0 with D>=n-pi(n) for all n. A transducer
reading n initial zeros emits max(0,n-D) zeros. It retains the
exact n through a finite initial range and thereafter only n
modulo m. Upon seeing the first 1, it emits

    pi(n)-max(0,n-D)

additional zeros, then 1, and copies the remaining suffix. The
number of additional zeros is nonnegative. It is determined by
the finite state: for large n it is D plus the periodic offset
pi(n)-n, and the remaining cases are a finite table. The all-zero
input produces infinitely many zeros after the initial delay.
This is a finite-state deterministic asynchronous realization.
The inverse permutation has the same eventual ray structure, so
the inverse homeomorphism has such a realization as well.
