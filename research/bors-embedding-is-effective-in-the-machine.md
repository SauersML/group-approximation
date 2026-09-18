---
rg: 2
id: bors-embedding-is-effective-in-the-machine
kind: claim
title: The Birget-Ol'shanskii-Rips-Sapir embedding is computable from the accepting machine
distinct_from:
  quantitative-higman-embedding-with-dehn-control: that imports the existence and metric bounds of the BORS/Chornomaz-Wagner embedding for one group; this records that the finite presentation of the host and the embedding words are computed from the accepting Turing machine alone, uniformly, which is the property a halting reduction consumes.
  np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups: that asks for a simple polynomial-Dehn host for each NP input; this is about the non-simple BORS host and only asserts that its construction is an algorithm in the machine.
---

**ESTABLISHED by citation (unreviewed).**  There is an algorithm which, given a
non-deterministic Turing machine `M` over an alphabet `A = A_0 u A_0^-1`
(`A_0` finite), outputs a finite presentation `P(M)` of a group `H(M)` and, for
each `x in A`, a generator `b_x` of `P(M)`, with the following property.

> If the language accepted by `M` is the set of words equal to `1` in some
> group `G = <A_0>`, and the time function of `M` is bounded by `T(n)` with
> `T(n)^4` superadditive, then `x -> b_x` induces an injective homomorphism
> `G -> H(M)` with bounded distortion, and the Dehn function of `P(M)` is
> equivalent to `n^2 T(n^2)^4`.

The conditional clause is Birget--Ol'shanskii--Rips--Sapir Theorem 1.1 together
with their Lemma 4.35.  The algorithmic clause is the new content: the
presentation `H_N(S)` of BORS Section 3 is written down from finite data --
the S-machine `S = S(M)` of Sapir--Birget--Rips Section 4, which is itself
constructed from `M`, and the integer `N = 9ck`, which BORS computes from `S`.
No step of the construction consults the language `L(M)`, the group `G`, or
the time bound `T`.  These enter only the *proofs* of the embedding and of the
Dehn bound.

In particular the construction applies to **every** machine `M`, and
`P(M)` is a total computable function of the code of `M`.  The conclusions
about `G` hold whenever the hypotheses do, whether or not anyone can verify
them.

**What is read from the source and what is inspection.**  The source states
Theorem 1.1, Lemma 4.35, the explicit generators and relations of `H_N(S)`, the
choice `N = 9ck`, and the procedure "construct a Turing machine ..., then
convert it into an S-machine, then convert the S-machine into a group".  It
does not contain a sentence of the form "the map `M -> P(M)` is recursive".
That uniformity is read from the explicit constructions quoted in the citation
route, each of which is a finite syntactic transformation of finite data.

DERIVATION
bors-embedding-is-effective-in-the-machine-citation
