---
rg: 2
id: bcv-one-group-trace-and-embedding-boundary-proof
kind: route
title: Compare regular characters under subgroups quotients and the negative Pauli corner
target: bcv-one-group-trace-and-embedding-boundary
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
  - clapham-fp-embedding-preserves-word-problem
  - bcv-pauli-amplification-haarizes-only-the-packet
  - gowers-hatami-finite-group-hs-stability
---

For \((\mathrm{BTE1})\), the canonical group trace is the coefficient of the
identity in the left regular representation. A word-problem decider therefore
computes it exactly.

For \((\mathrm{BTE2})\), let the known distance between \(K_0\) and \(K_1\)
be greater than \(3\epsilon>0\). Uniform computability of the moments gives
an approximation \(z_M\) with
\(|z_M-\tau(w_M)|<\epsilon\). Exactly one of the two closed sets lies within
\(\epsilon\) of \(z_M\), so this finite computation decides whether \(M\)
halts.

For \((\mathrm{BTE3})\), injectivity gives

\[
 \iota(g)=1_H\Longleftrightarrow g=1_G.
\]

Apply the identity-coefficient formula for the two canonical traces.
Clapham's theorem supplies a finitely presented host and a host decider only
from an input group already equipped with a decider. Ordinary effective
Higman embedding starts from a recursively enumerable presentation and
does not have that conclusion. These are algebraic embeddings; their
statements contain no perturbation, basis, or matrix-rounding assertion.

For \((\mathrm{BTE4})\), choose \(1\ne n\in\ker\pi\). Then
\(\pi(n)=1_Q\), proving the two displayed moment values. Thus even when a
word in the generators of \(Q\) is represented by a computable lift to
\(H\), testing its pullback-trace value is exactly testing whether its image
is trivial in \(Q\). Host canonical microstates converge to
\(\tau_H\), not to this pullback character. The cited hyperlinear
group-factor equivalence is explicitly canonical-trace preserving and
contains no assertion about arbitrary quotient characters.

Finally, let \(J\) be a nontrivial central involution. Canonical trace gives
\(\tau(J)=0\), so

\[
 p_-=\frac{1-J}{2},\qquad \tau(p_-)=\frac12,\qquad
 Jp_-=-p_- .                                               \tag{BTP1}
\]

The normalized corner trace \(\tau_-(x)=2\tau(x)\) therefore has
\(\tau_-(Jp_-)=-1\). A trace-preserving embedding of \(L(\Gamma)\) into a
hyperfinite tracial ultrapower restricts to a trace-preserving embedding of
\(p_-L(\Gamma)p_-\) into the corresponding finite corner. Hence the
negative sector has canonical-profile matrix approximants.

These approximants still satisfy the group and corner relations only in
normalized \(2\)-norm. Gowers--Hatami can flexibly correct the complete
multiplication table of the finite Pauli group. It says nothing about the
arbitrary commutant representation which carries the decoded source.
Equations \((\mathrm{PHT5})\)--\((\mathrm{PHT9})\) of
bcv-pauli-amplification-haarizes-only-the-packet show explicitly that all
zero-translation source moments survive in that multiplicity trace.
Moreover ordinary unitary correction does not impose BCV's common
Z-aligned signed-permutation basis. Thus the trace-safe central cut and the
finite packet correction both stop before the required exact ZPC object.
