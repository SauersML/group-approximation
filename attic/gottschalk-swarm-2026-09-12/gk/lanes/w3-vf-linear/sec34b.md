
### 34.6 The §33 scope fix (w7-v-cycle-c3, a886f33f26): PASS

* **What changed.** Four files.
  * **Claim node** `p-cycle-tree-invariance-cannot-force-order-char-law`. The title, `distinct_from`, "Why it matters"
    and the Attempts entry now say elementary abelian `p`-subgroups: `E_infinity`, the trees `E_n`, and injective
    homomorphisms between them. A new "Not covered" bullet names `W = E_p ⋊ <s>` with `s ~ tau_1`.
  * **Artifact.** Changed: the Section 2 Consequence, the Section 3 bullet, "orbits of nontrivial characters" in
    Step 2, and "when `|I| >= 2`" in Proposition 2.3(4). Lemma 2.1 is now stated for conjugacy between subgroups of `E`.
  * **Gate node.** The w7-v-cycle-c3 entry cites the cylinder-group node as ESTABLISHED, and its law bullet is scoped.
    The w7-v-gate-c3 entry is unchanged.
  * **Law node.** The w7-v-cycle-c3 entry is scoped.
* **Check.**
  * Every place §33.3 listed is scoped.
  * Claim items 1–6 are unchanged.
  * The italic verification lines are intact.
  * The new bullets say exactly what §33.3 records as not covered.
* **Status.** Claims 1–6 are direct computations:
  * the `exp_m` homomorphism;
  * the Lemma 2.1 substitution;
  * the kernel `u^(m−1) L`;
  * `w_m = m(d_(m−1) − d_m)`;
  * Schwartz–Zippel;
  * the arithmetic of item 5. At `j = m` the law forces `phi = 1`, contradicting `j = 1`. `1/m = phi + (1 − phi) p^(-r)`
    for all `r` forces `m = 1`.

  They use no other claim, so the route `p-cycle-tree-invariance-cannot-force-order-char-law-proof` has
  `requires: []`. The "First premise broken" paragraph uses [TS] Lemma 1.1 and Theorem 1.1, but it comments on where
  the models stop and is not a claim item. w7-v-cycle-c3 handed the status change to this lane, so this landing adds
  the route and marks the claim ESTABLISHED.
