# Filter the fibre by open normal subgroups and pass finite-fibre cost equality through increasing-factor continuity

*Attempt artifact (2026-09-17), formerly route `fpbs-profinite-skew-products-reduce-to-finite-fibers-proof` into `fpbs-profinite-skew-products-reduce-to-finite-fibers`, requires `fpbs-traffic-variational-cost-identities` and `fpbs-finite-fiber-cost-bound`. Taken out of the graph because referee lenses 1 and 2 of three returned *refuted*. All three lenses checked parts (a) and (b) and the conditional first sentence of (c). Lens 2 refuted the second sentence of (c): `fpbs-finite-fiber-cost-bound` proves (F)<=>(I) only over a class of groups, and (I)=>(F) passes through the different group Gamma x Sym(q), so the per-Gamma equivalence fails. Lens 2 also found the isometric-extension theorem stated in the wrong direction, and the residue misidentified: the chain argument needs K^0 <= L, not K^0 trivial. Lens 1 refuted the hole reframing's claim that the recorded rounding countermodels are all finite-fibre. Lens 3 returned *survives*. Restore this as a route once those are fixed and a full referee pass survives.*

Artifact Section 4, Theorem 4.1.

**Uniform finite fibres.** L K_n is open, hence of finite index. The
quotient map kL -> k L K_n is K-equivariant, so it intertwines the skew
product actions. It pushes m_{K/L} to the uniform measure on
K/(L K_n). So Z -> Z_n -> W, with uniform finite conditional fibres over
W.

**Generation.** The closed sets L K_n decrease to L by compactness. The
countably many quotient maps therefore separate the points of the
standard Borel space K/L. They generate its Borel sigma-algebra, and so
the Z_n generate Z.

**Continuity.** All spaces are free, being extensions of W, and C(W) is
finite. Section 10 of `fpbs-traffic-variational-cost-identities` gives
C(Z_n) decreasing to C(Z). Under uniform finite-fibre preservation each
C(Z_n) = C(W), so C(Z) = C(W). The equivalence of that hypothesis with
finite-index multiplicativity is `fpbs-finite-fiber-cost-bound`.
