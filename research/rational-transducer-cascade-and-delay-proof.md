---
rg: 2
id: rational-transducer-cascade-and-delay-proof
kind: route
title: Compose a finite cascade and check a bounded residual word at each reachable state
target: rational-homeomorphism-subgroups-have-exponential-wp
requires: []
artifacts:
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
---

## Model

Use the deterministic asynchronous transducer model of
[Belk--Bleak, Definition 5.1](https://arxiv.org/html/1405.0982#S5):
each transition reads one input letter, changes state, and outputs a
finite word, possibly empty. A nondegenerate transducer produces
infinite output on every infinite input. Invertible rational maps form
a group, so inverse generators also have fixed finite transducers.
The complexity argument below is written out independently.

Fix transducers for a finite symmetric generating set. Let s>=2 bound
their state counts, let l>=2 bound their per-transition output lengths,
and let d=|A|. These are constants, independent of the input word.

## The cascade

For a product of n generators, keep the tuple of their n current
states. Feed an input letter to the first transducer, its output word
to the second, and so on. This gives a transducer with at most

    N=s^n states,       L=l^n output letters per transition.

All transition entries can be constructed in time bounded by a
polynomial in n times (s*l)^n: processing a word of length k through
one fixed transducer takes O(k), and the intermediate lengths are
at most l,l^2,...,l^n. The order of the factors is chosen to agree
with the convention for composing homeomorphisms. The cascade is
nondegenerate because each of its factors is.

## Identity test for one explicit transducer

Let T have N states and maximum output length L. Explore the reachable
state graph breadth first, starting at the initial state q_0. Give
q_0 the empty residual word D(q_0). On a transition

    (q,a) -> (r,w),

require w to be a prefix of D(q)*a. If it is, remove w and obtain
a proposed residual word D_new for r. If r is new, assign D(r)=D_new.
If r has already been visited, require D_new=D(r). Reject on any
failed requirement, and otherwise accept after all reachable
transitions have been checked.

Here is a proof of the test, including the case of delayed output.
For an input prefix u, let v be the finite output already produced
and q the reached state. If T defines the identity on A^N, then v
must be a prefix of u. Otherwise v either already disagrees with u
or extends beyond u; in the latter case an input continuation using
a different next letter contradicts identity. Thus

    u=v*D_u.

The output function from q must satisfy T_q(z)=D_u*z for every
infinite continuation z. Two different words D_u cannot satisfy
this equation at the same state: if D*z=D'*z for all infinite z,
then D=D', since the alphabet has at least two letters. Therefore
identity forces exactly the transition and consistency checks above.

Conversely, if all checks pass, induction on input length gives
u=v*D(q) for every input prefix. A state's assigned residual comes
from its first breadth-first path, whose length is at most N-1.
Consequently every assigned residual has length at most N-1. Along
any infinite input, the output is always a prefix of that input
and its length is at least the input-prefix length minus N-1.
It follows that the infinite output equals the input. This proves
sufficiency, even without a separate productivity test.

There are at most d*N transitions to inspect. Each word comparison
uses O(N+L) time, and breadth-first traversal and residual storage
are polynomial in N+L. A conventional Turing-machine implementation
may add polynomial overhead, which does not affect the conclusion.

## Word-problem bound and embeddings

Apply this identity test to the cascade. Both N and L are exponential
in n, so the total deterministic running time is 2^O(n).
If a finitely generated abstract group embeds in the rational group,
fix transducers for the images of its generators and inverses. This
algorithm decides its word problem. An algorithm for finding the
embedding is unnecessary: the finitely many image transducers are
fixed constants in the resulting decision algorithm.

This is a proof of an upper bound, not a claim that the bound is optimal.
It decides equality, not element order or conjugacy. It is compatible
with undecidability of other problems in the rational group.
