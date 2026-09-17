# Baire category on the compact spaces of uniformly nonamenable marked groups

*Attempt artifact (2026-09-17), formerly route `fpbs-l2-gap-baire-dichotomy-proof` into `fpbs-l2-gap-baire-dichotomy`, requires [fpbs-l2-gap-class-closed-under-local-limits]. Demoted from the graph because referee lenses 1 and 3 returned *refuted* on one sentence of the claim: "a failure of the l2 gap on Cayley graphs is never isolated in the marked-group topology" (repeated in Section 2, Consequences, of the source artifact as "never isolated: it comes with a perfect-type family"). Theorem 2.2(iv) gives only that `K \ C_2` is comeager in `K`, and an isolated point of `X_(k,eta)` outside `C_2` (for example a marking of a finitely presented simple nonamenable group, such as Thompson's `T`, if it fails the gap) would be a singleton kernel component. All three lenses found Lemmas 1.1, 1.2 and Theorems 2.1, 2.2 sound. Restore it as a route once that sentence is deleted or restricted to the perfect part of `K` and a full referee pass survives.*

Source: `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`, Sections 1 and 2.

1. **Compactness (Lemma 1.1).** By Fekete, `rho = sup_n p_{2n}(o,o)^{1/(2n)}`.
   Each `p_{2n}(o,o)` is determined by the rooted `n`-ball, so `rho` is lower
   semicontinuous on the compact space of `k`-marked groups, and
   `{rho <= 1-eta}` is closed. Members are infinite, since a finite graph has
   `rho = 1`.
2. **Closed pieces (Lemma 1.2).** Theorem 3.1(c),(d) of
   `fpbs-l2-gap-class-closed-under-local-limits` gives that each
   `U_{M,delta}` is closed under local limits of infinite transitive graphs,
   and that `C_2 = union_{M,j} U_{M,1/j}`. Monotonicity (F1) gives
   `U_{M,delta} subseteq U_{M',delta'}` for `M <= M'` and `delta' <= delta`.
3. **Dichotomy (Theorem 2.1).** A compact metrizable space is Baire. If no
   closed piece has interior in `Y`, then `Y cap C_2` is a meager `F_sigma`, so
   its complement is a dense `G_delta`. An open patch lies inside `C_2`, so the
   two cases exclude each other.
4. **Kernel (Theorem 2.2).** The derivative strictly decreases closed sets,
   and in a second countable space this happens only countably many times.
   Removed points lie in open patches, hence in `C_2`. On the kernel the
   derivative is the identity, so case (a) fails and case (b) holds.
   Compactness gives a finite subcover, and Lemma 1.2 then gives the uniform
   version.
