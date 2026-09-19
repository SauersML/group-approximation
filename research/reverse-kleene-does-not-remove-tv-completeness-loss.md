---
rg: 2
id: reverse-kleene-does-not-remove-tv-completeness-loss
kind: claim
title: Reverse Kleene does not turn Taller--Vidick near-completeness into algebraic survival of J without a proof-gap crossing theorem
artifacts:
  - research/artifacts/taller-vidick-reverse-kleene-endpoint-audit-2026-08-21.md
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for the missing exact LCS compiler; this audits the tempting recursion-theorem upgrade and isolates the additional implication it would need.
  halt-now-certificate-area-still-needs-a-crossing-envelope: that is the general moving-window matrix-microstate firewall; this is the solution-group specialization, where a formal proof of `J=1` supplies an instance-dependent game gap but Taller--Vidick's noise was fixed before that proof is found.
  threshold-free-reverse-kleene-higman-diagonal: that works because HALT gives qualitative algebraic survival of the mark; Taller--Vidick gives only one near-perfect strategy and therefore does not supply its HALT clause.
---

Apply the recursion theorem to a machine which searches for a formal proof
that the distinguished central involution `J` is trivial in its own
Taller--Vidick output solution group.  If the machine does not halt, then
`J!=1`; Taller--Vidick's NONHALT soundness gives a constant quantum-value gap,
so this branch would indeed produce a nonhyperlinear solution group.

The halting branch does not contradict the published completeness theorem.
A found derivation `D` of `J=1` gives a computable, presentation-dependent
number `gamma(D)>0` such that every finite-dimensional strategy has value at
most `1-gamma(D)`: telescope the approximate solution-group relators along
`D` and use the standard LCS strategy-to-approximate-representation estimate.
But Taller--Vidick supplies only value at least `1-epsilon`, where `epsilon`
was fixed before `D` was found.  A contradiction follows only from the new
crossing assertion

```text
epsilon < gamma(D).                                      (TVK1)
```

Proof enumeration and self-reference do not imply `(TVK1)`.  If the machine
waits only for proofs satisfying it, failure to halt no longer implies
`J!=1`.

The paper's noise parameter cannot be sent algebraically to zero.  For every
`epsilon>0` its Bernoulli mask has full support on all mask functions, whereas
at `epsilon=0` the support collapses to the single constant-one mask.  Thus
the associated solution-group presentation changes discontinuously at zero.
Moreover the soundness decoder's factor is `4 epsilon delta^2` and vanishes
at zero, while the theorem chooses a repetition count `u=u(epsilon)`.  The
published construction supplies no homomorphisms transferring a proof
`J=1` between the changing `u`-presentations with a controlled proof gap.

For fixed `(u,B,pi)`, the support is in fact constant throughout positive
noise; `taller-vidick-positive-noise-fixed-support-reweighting` records this
sharper statement.  It does not repair the argument: reweighting preserves
strict soundness but multiplies honest loss by an inverse rare-mask weight,
the weighted van Kampen gap depends on the eventual certificate, and the
published soundness choice `(TVF9)` varies `u` with `epsilon`.

Therefore a reverse-Kleene upgrade needs a genuinely new nested-transfer or
uniform proof-gap theorem; it does not follow from
`LIN*_(1-epsilon,s)=RE`.  The full fixed-point audit is

For fixed `(u,B,pi)`, the support is constant throughout positive noise;
`taller-vidick-positive-noise-fixed-support-reweighting` records the
reweighting and weighted-certificate estimates. Reweighting cannot repair
completeness because it leaves the two contradictory parity equations in
the support. Deleting them reaches a different zero-noise presentation and
loses the published decoder.

## Coherent refinements cannot repair old rare rows

The same two-row certificate rules out a diagonal tower in which a later
honest tuple is required to approximate **all** relators of an earlier
positive-noise output.  Write the two earlier equations as

\`\`\`text
L=J^a,                    L=J^(a+1).                    (TVK2)
\`\`\`

For any unitary evaluation with \`J=-I\`, put
\`X=(-I)^a L(U)\`.  Normalized Hilbert--Schmidt norm satisfies the exact
parallelogram identity

\`\`\`text
||X-I||_2^2+||X+I||_2^2=4.                             (TVK3)
\`\`\`

Consequently at least one of the two row defects in \`(TVK2)\` is at least
\`sqrt(2)\`.  This lower bound is independent of the later dimension, the
earlier proof length, the repetition count, and both noise parameters.
Thus no sign-preserving sequence of later observables can have maximum
defect tending to zero on every earlier row.

There is an equivalent exact obstruction.  Since \`J=1\` in every
positive-noise solution group, no group homomorphism from an earlier output
to a later marked solution group can send the earlier \`J\` to a nontrivial
later sign.  A proposed approximate marked homomorphism is blocked
quantitatively by \`(TVK3)\`.

The only way a refinement can evade this wall is to delete at least one
member of every antipodal mask pair.  That is a support change, not a
smaller positive weight: at zero noise the row disappears, while the
published Fourier soundness factor disappears with it.  Hence choosing a
later \`epsilon_n\` after discovering the length of an earlier van Kampen
proof cannot work.  The obstruction has area two and constant unweighted
defect before any proof-length estimate is used.

Therefore a reverse-Kleene upgrade needs genuinely new finite equations or
a new zero-noise decoder. It does not follow from
`LIN*_(1-epsilon,s)=RE`. The earlier source audit is retained in
`taller-vidick-reverse-kleene-endpoint-proof`.
