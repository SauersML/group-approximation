---
rg: 2
id: fpbs-l2-gap-baire-dichotomy
kind: claim
title: On compact sets of uniformly nonamenable marked groups the l2 gap either has a uniform patch or fails generically, and a derived kernel carries every failure
distinct_from:
  fpbs-l2-gap-class-closed-under-local-limits: that proves each uniform class U_(M,delta) is closed and C_2 is F_sigma; this uses those facts on the compact spaces X_(k,eta) to get a Baire dichotomy, a countable-rank derived kernel, and the equivalences C_2 = X_(k,eta) iff the kernel is empty and uniform constants iff the first derivative is empty.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures the critical l2 bound on every nonamenable transitive graph; this proves no bound and only restates the Cayley-graph gap version as emptiness of a kernel, with generic failure on the kernel if it is nonempty.
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
  - research/artifacts/fpbs-l2-gap-baire-dichotomy-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof (Theorems 2.1 and 2.2 of
`research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`) is recorded as an
attempt (see Attempts). It is not established because two referee lenses
refuted the claim as written: the closing "never isolated" sentence does not
follow from the theorems.

For `k >= 1` and `eta in (0,1)` let `X_{k,eta}` be the space of `k`-marked
groups whose simple Cayley graph has spectral radius at most `1 - eta`. It is
compact, and its members are infinite nonamenable groups. Let
`U_{M,delta} = {G : ||T^G_{p_c(G)+delta}|| <= M}` and
`C_2 = {p_c < p_{2->2}}`, as in `fpbs-l2-gap-class-closed-under-local-limits`.

1. **Dichotomy.** For every nonempty closed `Y subseteq X_{k,eta}`, exactly one
   holds:
   * (a) some `U_{M,delta}` contains a nonempty relatively open subset of `Y`;
   * (b) `Y \ C_2` is a dense `G_delta` subset of `Y`.
2. **Kernel.** Remove from `Y` every relatively open set contained in some
   `U_{M,delta}`. Iterate transfinitely, starting from `X_{k,eta}` and
   intersecting at limit stages. The iteration stops at a countable ordinal,
   at a closed set `K_{k,eta}`. Then:
   * `X_{k,eta} \ C_2 subseteq K_{k,eta}`;
   * `X_{k,eta} subseteq C_2` if and only if `K_{k,eta}` is empty;
   * if `K_{k,eta}` is nonempty, then `K_{k,eta} \ C_2` is a dense `G_delta`
     in `K_{k,eta}`;
   * every marked group in `X_{k,eta} \ K_{k,eta}` has
     `p_c < p_{2->2} <= p_u`.
3. **Uniform version.** There are `M` and `delta` with
   `X_{k,eta} subseteq U_{M,delta}` if and only if the first derivative is
   empty, that is, if and only if every point of `X_{k,eta}` has a
   neighbourhood inside some `U_{M,delta}`.

This is a reframing, not a proof of any gap. It says that a failure of the l2
gap on Cayley graphs is never isolated in the marked-group topology: it lies in
a kernel on which failures are comeager. Any fixed-constant certificate on an
open set of marked groups shrinks the kernel.

## Attempts

1. **Baire category on the compact spaces of uniformly nonamenable marked
   groups (2026-09-17).** Formerly the route `fpbs-l2-gap-baire-dichotomy-proof`
   (requires [fpbs-l2-gap-class-closed-under-local-limits]); see
   `research/artifacts/fpbs-l2-gap-baire-dichotomy-proof-attempt-2026-09-17.md`
   and Sections 1 and 2 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.
   Demoted on 2026-09-17 after the referee pass. Lenses 1 and 3 refuted; lens 2
   survived (verdict 22905b4a). All three found Lemma 1.1, Lemma 1.2,
   Theorem 2.1 and Theorem 2.2(i)-(vi) sound, so items 1-3 above are expected
   to stand once the last paragraph is repaired. Refutation reasons:

   Referee lens 1 (refuted, verdict 79d6ad30):

   > The claim body says a gap failure on Cayley graphs "is never isolated in
   > the marked-group topology". Artifact Section 2, "Consequences", says a
   > counterexample "is therefore never isolated: it comes with a perfect-type
   > family." Theorem 2.2(iv) gives only that K\C_2 is comeager in K, and
   > nothing forces K to have no isolated points. Take a point x that is
   > isolated in G_k, lies in X_(k,eta), and is not in C_2. Then {x} is open,
   > but no U_(M,delta) contains it, so no derivative ever removes x. So K={x}
   > is consistent with every theorem, and comeagerness in K says nothing.
   > Such isolated points exist: finitely presented simple groups are isolated
   > in the space of marked groups, and Burger–Mozes lattices are nonamenable
   > examples. Repair: delete the "never isolated / perfect-type family"
   > sentences, or restrict them to the perfect part of K. Items 1–3 can then
   > stand.

   Referee lens 3 (refuted, verdict 95bd5089):

   > Nothing proves this, and nothing supports it at isolated points. Take an
   > isolated point x of X_(k,eta) with x not in C_2. Then x is never removed,
   > and {x} is an open subset of the kernel K containing no other failure. If
   > every other point is removed, K = {x}, and "comeager in K" says nothing.
   > The established claim fp-simple-groups-are-isolated shows finitely
   > presented simple groups are isolated. Thompson's T is one: it is infinite
   > and nonamenable, so some marking of it lies in some X_(k,eta), and whether
   > it is in C_2 is open. So the sentence is really the open statement "every
   > isolated point of X_(k,eta) is in C_2", presented as a consequence.
   > Repair: delete the sentence, or restrict it to "failures at non-isolated
   > points of K are not isolated in K". Items 1-3 of the claim can stay as
   > they are.
