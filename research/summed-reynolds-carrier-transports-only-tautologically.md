---
rg: 2
id: summed-reynolds-carrier-transports-only-tautologically
kind: claim
title: The summed Reynolds carrier transports through every Kac--Moody chart only by collapsing to the tautological full carrier
distinct_from:
  summed-reynolds-cut-synchronizes-kernel-corners: that constructs one P_0-invariant spectral carrier and polar-corrects every compressed kernel word; this proves that the carrier and all of those polar corrections already extend to the full ambient corner with explicit dimension-free cost.
  triangle-kernel-relators-charge-authenticated-corner-leakage: that controls Julia leakage after a compressed word has been matched to native chart paths; this shows why the Reynolds construction by itself supplies only the tautological paths I and pi(n_a), not the independently exactified P_13 chart path needed for that match.
  relative-three-chart-correction-is-km-regular-stability: that identifies exact simultaneous overlap correction with the terminal global theorem; this closes the intervening projection-transport question and localizes the remaining content entirely in a comparison of corrected chart coefficients.
  one-state-protected-coefficient-leaves-relative-gh-gauge: that proves one full-trace unitary coefficient would fix the relative P_13 gauge with constant one, whereas one faithful state-dependent coefficient leaves an asymptotically maximal amplified commutant gauge.
---

**ESTABLISHED.**  In the notation of
`summed-reynolds-cut-synchronizes-kernel-corners`, put

```text
alpha=E/s,                 beta=tr(q)>=1-alpha.          (SRT1)
```

All normalized `L^2` norms below are ambient unless a corner is displayed.
Then

```text
||q-I||_2<=sqrt(alpha),                                  (SRT2)
||[U,q]||_2<=sqrt(2 alpha)       for every unitary U,    (SRT3)
||qY_aq-Y_a||_2<=2sqrt(alpha),                           (SRT4)
||qY_aq-q||_2<=sqrt(E).                                  (SRT5)
```

In particular the replacement carrier `q'=I` is exactly invariant under
`P_1`, `P_3`, all three rank-two vertex charts, and every overlap gauge.  It
loses no regular mass when the ambient finite-subgroup charts are regular,
and it differs from the Reynolds carrier by at most `sqrt(alpha)`.  Thus
transport of the **projection** through the rank-two charts is automatic and
dimension-free; no alternating-Reynolds or common-commutant theorem is
missing at that level.

The polar corrections transport just as tautologically.  Extend each
`B_a in qM_Dq` by the identity on `(I-q)C^D`:

```text
tilde B_a=B_a+(I-q).
```

Then `tilde B_a` is a global unitary and

```text
||tilde B_a-I||_2<=2sqrt(beta |H|s),
||tilde B_a-tilde B_b||_2<=4sqrt(beta |H|s).             (SRT6)
```

For the optimized choice `s=sqrt(E)`, the carrier-transport cost is
`E^(1/4)` and every extended polar correction is `O_H(E^(1/4))` from the
identity.

This does **not** identify the required Kac--Moody multipath coefficient.
On the full carrier the only paths supplied by the construction are the
tautological native pair

```text
I, Y_a=pi(n_a),       K_a^full=(I+Y_a)/2,               (SRT7)
```

whose disagreement is already `||Y_a-I||_2<=sqrt(E)`.  The polar unitary
`tilde B_a` is obtained from singular-value completion and has no reason to
be a word, a finite-label path, or the path coming from the independently
Gowers--Hatami-exactified `P_13` chart.  The Reynolds inequalities contain no
term involving that corrected chart, so they cannot bound its distance to
`tilde B_a`.

This last independence has an exact finite-dimensional model.  In the local
regular counterpackets of
`km-triangle-local-bimodules-have-finite-nonflat-models`, amplify the
`P_13` chart and multiply one of its overlap identifications by an arbitrary
unitary in the regular multiplicity commutant.  The tree-side representation,
all `Y_a`, `Delta`, `q`, and `B_a` are unchanged, as are every finite local
table and overlap intertwining equation.  The returned corrected-chart path
coefficient changes by the arbitrary commutant unitary.  Hence no estimate
whose hypotheses mention only the summed Reynolds data can identify that
coefficient, even in exact finite dimensions.  A successful comparison must
add the choice/coherence data of the finite-group exactification itself.

Consequently the narrowed Kac--Moody bridge is no longer carrier transport:
it is a **relative coefficient comparison theorem**.  One must construct the
finite-group exactification of the section chart together with a comparison
partial isometry whose two `P_1`/`P_3` path coefficients are close to
`tilde B_a` (or directly to each other) on positive regular mass.  Such a
theorem is exactly where the native kernel relations must enter; another
spectral cut or invariance argument cannot provide it.

The strength of the required protection is now classified by
`one-state-protected-coefficient-leaves-relative-gh-gauge`.  Since
`tilde B_a` is a full ambient unitary, normalized-HS control of the single
operator coefficient `Q_2 tilde B_a Q_1^*` fixes the relative gauge with
constant one.  State-dependent control does not: even a faithful density can
ignore a trace-large amplified complement.  Thus a relative exactification
must protect this coefficient in ambient trace norm, or prove a uniform
density domination which upgrades its state seminorm to that norm.
