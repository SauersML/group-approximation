---
rg: 2
id: bcv-one-group-trace-and-embedding-boundary
kind: claim
title: Canonical search survives decidable subgroup embeddings but not quotient traces or BCV exactness
distinct_from:
  bcv-pauli-amplification-haarizes-only-the-packet: that computes the exact packet/source trace factorization inside one perfect strategy; this audits which of those traces can be obtained from the canonical trace of a single group.
  clapham-fp-embedding-preserves-word-problem: that supplies a decidable finitely presented overgroup; this shows exactly what canonical-trace data the embedding preserves and what it does not exactify.
  trace-functorial-bcs-signal-groupification-impossible: that rules out an exact trace-functorial decoder by applying it to the regular trace; this separates subgroup canonical traces, quotient pullback traces, central corners, and effective HALT signals.
  bcv-universal-halt-canonical-microstate-exactification: that is the positive open bridge sufficient for the diagonal; this records why trace selection and standard embeddings do not establish it.
---

**ESTABLISHED BOUNDARY.** The following four facts constrain any attempt to
put the universal BCV HALT family into one group.

## 1. Canonical trace and effective trace signals

For a group \(\Gamma\) with decidable word problem, its canonical moments are
computable with an exact gap:

\[
 \tau_\Gamma(w)=\mathbf 1_{\{w=_{\Gamma}1\}}.             \tag{BTE1}
\]

This is precisely why the rational canonical-microstate search can decide
which strict test to impose.

Let \(\tau\) be any trace whose moments on a computable sequence of words
\(w_M\) are uniformly computable. If two computably specified closed subsets
\(K_0,K_1\subset\mathbb C\) have a known positive rational distance and

\[
 M\text{ halts}\Longrightarrow\tau(w_M)\in K_1,\qquad
 M\text{ does not halt}\Longrightarrow\tau(w_M)\in K_0, \tag{BTE2}
\]

then the halting problem is decidable: approximate the moment more accurately
than one third of the gap. Thus a computable, uniformly gapped scalar trace
packet cannot itself carry the HALT bit.

A computable faithful trace without an effective lower separation modulus
does not contradict this statement. Its positive values on nonidentity
elements may tend to zero noncomputably, and hyperlinearity of a group does
not in any case assert Connes embeddability of every noncanonical trace.

## 2. Injective embeddings preserve the canonical trace

For an injective homomorphism \(\iota:G\hookrightarrow H\),

\[
 \tau_H(\iota(g))=\tau_G(g) \quad(g\in G).                \tag{BTE3}
\]

Hence restriction along a computably specified subgroup embedding is
trace-safe. Clapham's decidability-preserving Higman refinement may be used
when a word-problem algorithm for the source is already supplied. Generic
effective Higman embedding gives a finitely presented host but does not
supply a host word-problem decider. Neither construction rounds approximate
representations to exact ones or makes their matrices signed permutations.

## 3. Rips quotients change the relevant trace

For a quotient \(\pi:H\twoheadrightarrow Q\) with nontrivial kernel, the
pullback of the quotient canonical trace is not the host canonical trace. For
\(1\ne n\in\ker\pi\),

\[
 (\tau_Q\circ\pi)(n)=1,\qquad \tau_H(n)=0.                \tag{BTE4}
\]

Consequently canonical microstates for a hyperlinear Rips host do not
approximate the quotient trace required to read quotient equality. If the
quotient has undecidable word problem, the moments
\((\tau_Q\circ\pi)(w)\) themselves decide that word problem. A Rips kernel
can hide the undecidability as kernel membership, but it does not make the
trace computable. General quotient preservation of hyperlinearity is not
available as a replacement.

## 4. The Pauli corner is legitimate but still only approximate

If \(J\ne1\) is a central involution in \(\Gamma\), then
\(\tau_\Gamma(J)=0\), not \(-1\). The central projection
\(p_-=(1-J)/2\) has canonical trace \(1/2\), and its normalized corner trace
does satisfy \(J=-1\). Connes embeddability of \(L(\Gamma)\) passes to this
corner, so a negative-sector construction is not ruled out in principle.

What it supplies, however, is a sequence of **approximate** finite-matrix
corner models. The BCV packet calculation fixes the finite Pauli factor in
that corner but leaves the source multiplicity trace and source relations
uncontrolled. Spectral cutting, Gowers--Hatami exactification of the finite
Pauli table, and Clapham/Higman embedding do not jointly produce an
attained-perfect Z-aligned signed-permutation strategy.

Therefore the only live one-group route is the explicit uniform
approximate-to-exact interface stated in
bcv-universal-halt-canonical-microstate-exactification. Canonical trace
computability, Higman/Clapham, Rips, and the Pauli corner each solve a
different local typing issue; none supplies that interface.
