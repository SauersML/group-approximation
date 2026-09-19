# A finite central group corner can never force proper infiniteness

Date: 2026-08-13

## The canonical-trace obstruction

Let \(G\) be a discrete group and let \(z\in Z(G)\) have finite order
\(m>1\).  For every character \(\chi:\langle z\rangle\to\mathbb T\), put

\[
 p_\chi=\frac1m\sum_{j=0}^{m-1}\overline{\chi(z^j)}u_{z^j}
 \in C^*(G).
\]

If the powers of \(z\) are distinct in \(G\), then the regular trace gives

\[
 \tau_G(p_\chi)=\frac1m>0.
\]

The image of \(p_\chi\) in \(L(G)\) is therefore a nonzero central
projection, and the normalized restriction

\[
 x\longmapsto m\tau_G(x),\qquad x\in p_\chi L(G)p_\chi,
\]

is a faithful finite trace.  Hence this corner is finite and contains no
properly infinite nonzero projection.

It follows that group relations alone cannot simultaneously retain a
nontrivial finite central phase and force its central-character corner to
be Leavitt/properly infinite.  Any such alleged identity would also hold in
the regular representation and contradict the displayed trace.

This explains the exact limitation of the atlas infinite-projection
certificates.  They prove proper infiniteness inside a particular Leavitt
coefficient representation, not in the corresponding central character
corner of every tracial group representation.  A nonhyperlinearity proof
must separate Connes-embeddable traces from the always-present regular group
trace; ordinary finite-von-Neumann-algebra positivity cannot do so.

