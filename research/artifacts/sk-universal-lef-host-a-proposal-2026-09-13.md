# sk-universal-lef-host-a: manuscript proposal (RULES §6), as amendments to sk-universal-lef-host-b's proposal

The base text is sk-universal-lef-host-b's corollary `cor:universal` (`research/artifacts/sk-universal-lef-host-b-proposal-2026-09-13.md`). It was landed first and covers the same mathematics, so this lane proposes no rival text. Target: rev3 §2 "LEF groups" (sk-editor-3). It is not on main yet; main's rev2 is e80dcf20ad.

## A1. The exact characterization (+2 source lines)
**(a) Current text**, peer proposal, statement of `cor:universal`:
```latex
Every countable LEF group is a subgroup of an infinite finitely generated
simple Kazhdan LEF group. One such group contains every recursively
presented finitely generated LEF group, for instance every finitely
presented residually finite group and every $G_Y$ whose language is
recursive.
```
**Replacement:**
```latex
Every countable LEF group is a subgroup of an infinite finitely generated
simple Kazhdan LEF group. A set of finitely generated groups lies in one
such group if and only if its members are LEF and represent countably
many isomorphism classes. So one such group contains every recursively
presented finitely generated LEF group, for instance every finitely
presented residually finite group and every $G_Y$ whose language is
recursive.
```
**(b) Proof.**
- The peer's proof already has both halves: the direct sum of representatives, and "a countable group has countably many finitely generated subgroups".
- Change its last sentence from "No countable group contains all finitely generated LEF groups, since …" to: "Conversely, subgroups of LEF groups are LEF, and a countable group has countably many finitely generated subgroups. There are continuum many groups $G_X$, so no such group contains all finitely generated LEF groups."
- This costs 0 lines.

**(c) Length:** +2 lines. **(d) Trade-off for the reader:** stronger at no cost in proof: a sharp iff in place of a one-sided statement plus an obstruction. **(e) Status:** `simple-kazhdan-lef-host-iff-lef-and-countably-many-types` (+proof), unreviewed, queued with sk-verify-7.

## A2. One construction for both §2 statements (about −6 source lines, optional)
- **Where:** rev3's §2 proof of the LEF characterization. It puts Γ in [Δ,Δ] through quotient doubling plus Ore (`rf-groups-lie-in-derived-subgroups-of-rf-groups`, part 2), then applies the lamplighter host.
- **Change:** in the peer's commutator-isolation paragraph, each $\iota(\gamma_j)=w_j(a,b)$ is a commutator, so it already gives $\Gamma\le[\Delta,\Delta]$ with $\Delta$ 2-generated and LEF. So: give the isolation paragraph once, state its conclusion as $\Gamma\le[\Delta,\Delta]$, and use it for the characterization (with $D=\Gamma$) and for the universal host (with $D$ the direct sum). The quotient-doubling paragraph goes.
- **Verbatim replacement for the closing clause of the peer's isolation paragraph:**
```latex
since $w_j(a,b)$ is the image of $\gamma_j$. Each $w_j$ is a commutator,
so $\Gamma$ lies in the commutator subgroup of this $2$-generated group.
```
- **(d) Trade-off for the reader:** shorter, and one argument serves both corollaries. The reader trusts nothing new.
- **(e) Status:** `lef-groups-embed-via-two-generator-lef-envelope` (route), unreviewed. The merged commutator sentence on `countable-lef-groups-embed-in-two-generator-lef-groups` is unreviewed. The lamplighter host node has three PASSes.

## Not proposed
- Hall's universal locally finite group as an example: recalled, not re-read.
- Rival LaTeX for the 2-generator lemma: this lane's Sym(m)≀Z/2^(2n+3) presentation is equivalent to the peer's levels presentation and no shorter.
