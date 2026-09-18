# The Belk–Hyde–Matucci pattern: criterion for unions, exact scope, and what GL_n(Q) would need (lane gq-bhm-pattern, 2026-09-17)

Sources:
- Belk–Hyde–Matucci, *Embedding Q into a finitely presented group*, arXiv:2005.02036 (Bull. AMS 59, 2022). The
  statements are as transcribed in `research/artifacts/gq-gq-lit-q-embeddings.md` §1.
- Landed nodes `lifts-add-no-unipotent-divisibility`, `gl-n-q-generated-by-gl-n-z-and-prime-dilations` and
  `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`.
- New nodes (this lane): `ascending-unions-embed-along-coherent-chains` and
  `sl-n-q-lies-in-one-factor-of-every-normal-series`.

## 1. The pattern in three moves

- **M1. A flexible ambient group with roots.**
  - In PL_2(R), every fixed-point-free element has n-th roots for every n (BHM Lemma 6).
  - The root is built on one fundamental domain [0, g(0)] and spread out by g.
- **M2. A finitely presented centralizer that captures the root tower.**
  - T̄ = C_{PL_2(R)}(z), where z(x) = x + 1.
  - If f^k = z^j, then f commutes with z, so f ∈ T̄.
  - Iterating Lemma 7 gives s_1 = z and s_m^m = s_{m-1}, all in T̄. So ⋃⟨s_m⟩ ≅ Q.
  - Abstractly: if an ambient group P is torsion-free, and every f with ⟨f⟩ ∩ ⟨z⟩ ≠ 1 has roots of every order
    in P, then C_P(z) contains a copy of Q through z. Finite presentation of C_P(z) is the only nonformal input. For T̄ it is
    immediate: T̄ is a central extension of the finitely presented group T by Z.
- **M3. The divisibility is central and splits across two layers.**
  - Q ≅ ⟨z⟩-by-(Q/Z), with ⟨z⟩ the centre of T̄ and Q/Z ≤ T ≤ V.
  - Both layers are Q-free. BHM Prop. 13 ("every subgroup of T̄ isomorphic to Q contains the center of T̄") shows
    this split is forced inside T̄.

In the language of `ascending-unions-embed-along-coherent-chains`, M1–M2 is the **extension form** of the union
criterion for H_m = (1/m!)Z and Γ = T̄. The next term of the chain is found inside Γ because Γ is defined as a
centralizer: the "closure under the extension problem" comes for free.

## 2. The union criterion (landed)

- H = ⋃H_m embeds in Γ iff there are embeddings ι_m: H_m → Γ whose restrictions agree exactly (extension form),
  or up to Γ-conjugacy (conjugacy form).
- Class form: if the chosen embeddings of H_m form one conjugacy class and restriction maps some member of the next
  class into it, then H embeds.
- Known instances:
  - BHM (extension form, via M2);
  - P. Hall's universal locally finite group (class form: isomorphic finite subgroups are conjugate).
- For the root: GL_n(Q) = ⋃ GL_n(Z[1/m!]). G(n) says one finitely presented simple Γ holds the whole chain,
  coherently up to conjugacy.

## 3. Exact scope of the pattern (landed obstruction)

`sl-n-q-lies-in-one-factor-of-every-normal-series`:
- Let E ⊇ SL_n(Q)/C, and take any finite series of normal subgroups of E. The first term containing SL_n(Q)/C
  gives a factor that is nonabelian and contains (Q,+). This factor holds a nontrivial perfect image of SL_n(Q),
  with every root group embedded.
- Hence no group whose factors are all abelian or Q-free contains GL_n(Q), SL_n(Q), PGL_n(Q) or PSL_n(Q). This
  consequence also follows from the earlier `extension-product-closures-cannot-create-sl-n-q`, whose class contains the
  abelian and Q-free groups and is closed under extensions. The new content is the localization of the factor.
- The proof is self-contained: a normal subgroup containing one root element is everything, using Lagrange's
  four squares for n = 2.

Consequences for route design:
- **M3 is unavailable for SL-type groups at any depth.** (Q,+) = Z-by-(Q/Z) is poly-(Q-free); SL_n(Q) is not
  even contained in a group with abelian-or-Q-free factors.
- **It closes the cover loophole.** Lifts through covers whose deck group contains Q, such as the adelic solenoid
  (R × A_f)/Q, give nothing over a Q-free base. `lifts-add-no-unipotent-divisibility` had left this case open.
- **Solvable targets behave differently.** Aff(Q), B_2(Q) and U_3(Q) are poly-abelian, so normal series cannot
  exclude them. `lifts-add-no-unipotent-divisibility` excludes them from the Q-free/central/Q-free shape. Its
  mechanism: a Q^x-stable subgroup of Q is 0 or Q, and a central element cannot be scaled by 2.

## 4. What a GL_n(Q) version must supply

- **N1. One nonabelian layer that already carries divisibility.**
  - By §3 the host (or the relevant factor) must contain a perfect group with root groups ≅ Q.
  - For a finitely presented simple host this is automatic. But no construction may obtain it by "divisibility
    from a lift" at any stage.
- **N2. A non-central root engine that respects dilations (the Aff(Q) core).**
  - GL_n(Q) contains Q ⋊_p Z for every prime p: the unipotent u = e_12(1) is conjugated to u^p by e_p = diag(p,1,...).
  - Any tower of roots of u used in M2 fashion must therefore be normalized by an element acting on it by
    multiplication by p, for every p at once.
  - The centralizer of u cannot capture these, and neither can the centralizer of any element of the tower: the
    dilation moves the tower.
  - The natural replacement is a finitely presented subgroup of the commensurator Comm_P(⟨u⟩) that is closed under
    "dilation-compatible roots". This is spark S1 of `gq-gq-lit-q-embeddings.md`.
  - **Test groups:** Q ⋊_2 Z (one prime), then Aff(Q). Both are excluded from T̄
    (`lifts-add-no-unipotent-divisibility`; directly, since in T̄ every Q contains z and z is central).
- **N3. Coherence for the arithmetic chain.**
  - GL_n(Q) = ⟨GL_n(Z), e_p (p prime)⟩, with the e_p commuting and free abelian of infinite rank
    (`gl-n-q-generated-by-gl-n-z-and-prime-dilations`).
  - A single host must carry GL_n(Z) together with an infinite commuting family (e_p), each acting as the
    prescribed Hecke correspondence on congruence subgroups.
  - In BHM, "infinitely many primes from finitely many generators" comes from rotation-type torsion of all orders
    in T. Here the needed elements e_p have infinite order and must be independent.
  - So a finitely generated mechanism producing infinitely many independent infinite-order elements with prescribed
    conjugation behaviour is required. Thompson-type groups contain Z^∞; the constraint is the relations with
    GL_n(Z), not the rank.
- **N4. Hosts already excluded:**
  - V (Q ⊄ V; O3);
  - VA and every subgroup of it for n ≥ 2 (O4, distortion);
  - T̄, and lifts of Q-free groups whose deck group is abelian (even containing Q) or Q-free (§3);
  - residually finite, linear and self-similar groups (O1).
  - Brin–Thompson nV contains Q (Kojima–Sheng arXiv:2603.18410v3); whether it contains SL_3(Z) is open on the
    boards (gq-nv-obstruct).

## 5. Sparks (not pursued here)

- **S-a.** A "commensurator engine": let P be a flexible ambient (Homeo_+(R), PL(R) with all rational slopes), and
  Γ ≤ Comm_P(⟨u⟩) finitely presented, containing dilations d_p with d_p u d_p^-1 = u^p. Is the tower of roots of
  u forced into Γ? The M2 argument used only "roots of a power of z commute with z". The analogue "roots of u^p are
  conjugate by d_p to roots of u" needs a uniqueness-of-roots statement in P that has not been checked.
- **S-b.** Use the class form with a Hall-type homogeneity in a finitely presented simple Γ. Look for a
  conjugacy-classification of "standard" embeddings of GL_n(Z[1/N]), for instance those given by Zaremsky's affine
  self-similar action on cones, that is stable under restriction from N·p to N.
