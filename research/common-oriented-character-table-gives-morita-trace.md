---
rg: 2
id: common-oriented-character-table-gives-morita-trace
kind: claim
title: A common oriented finite character table gives the prescribed-carrier Morita trace
distinct_from:
  hs-steinberg-morita-trace-additivity-on-adaptive-blocks: That is the open decoder face; this is a sufficient finite-table criterion for it.
  orthogonal-steinberg-root-spectral-support-is-not-additive: That assigns a separate spectral support to every root word; this uses subsets of one common PVM and therefore makes orthogonality literal.
  independent-address-capacity-cannot-drive-selected-atom-growth: That rules out tensor-independent address capacity as an amplifier; the table required here must be coupled to the payload and only decodes mass already present.
---

**ESTABLISHED CONDITIONAL DECODER.**  Fix a finite depth and the resulting
finite family `E` of named adaptive idempotents in
`finite-adaptive-selected-atom-ring-tree`.  Suppose every sufficiently good
normalized-HS microstate supplies:

1. one exact PVM `(P_chi)_(chi in Omega)` on the prescribed seed carrier
   `Q_*`, where `Omega` is a fixed finite set;
2. a subset `Omega_e subset Omega` for every `e in E`, and
   `P_e=sum_(chi in Omega_e) P_chi`;
3. whenever `qd=dq=0` is a named adaptive sum,

   ```text
   Omega_(q+d)=Omega_q disjoint_union Omega_d;          (OCT1)
   ```

4. whenever a named Murray--von Neumann arrow identifies `a` with `d`, its
   fixed Steinberg conjugator `W_(a,d)` satisfies

   ```text
   ||W_(a,d) P_a W_(a,d)^* - P_d||_2 <= eps;           (OCT2)
   ```

5. for the selected shared-BCS corner at every node,

   ```text
   tr(P_a)>=tr(Q_sigma P_i)-eps.                        (OCT3)
   ```

Here `eps=o(1)` is dimension-independent and tends to zero with the
presentation defect.  Then

```text
mu(e):=tr(P_e)                                         (OCT4)
```

satisfies `(MTA1)--(MTA3)` in
`hs-steinberg-morita-trace-additivity-on-adaptive-blocks`, with error at
most `eps`.  In particular, this finite common-table criterion is sufficient
for the fixed-depth non-hyperlinearity endpoint.

The common-table requirement is essential.  Separate spectral PVMs for the
individual root words do not imply `(OCT1)`, even in exact elementary-group
representations.  Nor can `Omega` be supplied as a tensor-independent bank
of address bits and then counted as new mass: the Kraft/capacity identity in
`independent-address-capacity-cannot-drive-selected-atom-growth` cancels that
apparent gain.  A successful construction must make the table orientation
payload-dependent while charging failure of `(OCT1)--(OCT3)` to the defining
relator energy.

