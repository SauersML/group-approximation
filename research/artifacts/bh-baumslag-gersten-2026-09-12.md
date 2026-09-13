# Boone–Higman for the Baumslag–Gersten group: host classes and obstructions

Lane `bh-baumslag-gersten`, swarm 7, 2026-09-12.

Convention as on main (`baumslag-gersten-base-is-elliptic-in-every-tree-action`):

    BG = BG_2 = < a, t | b a b^-1 = a^2 >,   b = t a t^-1.

`B = <a, b>` is a copy of `BS(1,2)`, and `BG` is the HNN extension of `B`
along `a -> b`. Main already records that `BG` is the smallest torsion-free
one-relator test case outside every class known to satisfy Boone–Higman. It is
not residually finite, contains `BS(1,2)` and so is not hyperbolic, and its
Magnus step has the non-free base `BS(1,2)`.

**Outcome.** Boone–Higman for `BG` is not settled. This lane lands two
obstructions to host shapes and maps the host classes that remain.

## 1. Every finite image kills `a` (classical; self-contained proof)

**Claim `baumslag-gersten-group-is-neither-linear-nor-self-similar`.**

Let `π: BG -> F` be a homomorphism to a finite group. Write `n = ord(π a)`.
Since `π b = π t · π a · (π t)^-1`, also `ord(π b) = n`. Iterating
`π b · π a · (π b)^-1 = (π a)^2` gives `(π b)^k π a (π b)^-k = (π a)^(2^k)`.
Taking `k = n` gives `π a = (π a)^(2^n)`, so `n | 2^n - 1`; in particular `n`
is odd.

Suppose `n > 1` and let `p` be the least prime factor of `n`. Then `2^n ≡ 1`
and `2^(p-1) ≡ 1 (mod p)`, so `ord_p(2)` divides `gcd(n, p-1)`. Every prime
factor of `n` is at least `p`, and every prime factor of `p - 1` is less than
`p`, so the gcd is `1`. That forces `2 ≡ 1 (mod p)`, which is impossible.

So `n = 1`: `a` lies in the kernel of every finite quotient. Since `a ≠ 1` in
`BG`, the group is not residually finite. Every finite quotient factors through
`BG / <<a>> ≅ Z` and so is cyclic, recovering Baumslag's 1969 theorem.

**Consequences.**
- **(L) Linear hosts.** By Malcev's theorem, finitely generated linear groups
  are residually finite, so `BG` is linear over no field. Neither
  `positive-char-linear-groups-satisfy-boone-higman` nor
  `char-zero-linear-groups-satisfy-boone-higman` can reach `BG`, even after
  enlarging the input.
- **(S) Rooted-tree and self-similar hosts.** `Aut(T)` of a locally finite
  rooted tree is residually finite: level stabilizers are normal of finite
  index and intersect trivially. So `BG` embeds in no such `Aut(T)`, hence in no
  self-similar group, hence in no finitely presented self-similar host. That
  rules out Zaremsky arXiv:2405.09722 Thm 1.1 as a route for `BG` or any group
  containing it, and matches `self-similar-hosts-contain-only-residually-finite-groups`.

## 2. Odometer pieces force fixed points (new, elementary; no novelty claimed)

**Claim `baumslag-gersten-odometer-pieces-force-fixed-points`.**

Let `BG` act by homeomorphisms on a Hausdorff space `X`. Suppose `Y ⊆ X` is a
compact metrizable subset with at least two points that is invariant under `a`
and `b`, and that `a|Y` is minimal and equicontinuous. Then `b` has a fixed
point `y ∈ Y`, and `a` fixes `t^-1 y`.

**Proof.**
1. A minimal equicontinuous homeomorphism of a compact metrizable space is
   conjugate to a minimal rotation `x ↦ x + θ` of a compact abelian metrizable
   monothetic group `K`, with `Zθ` dense (standard; e.g. Auslander, *Minimal
   Flows and their Extensions*, Ch. 3). Identify `Y = K`.
2. From `b a = a^2 b` on `Y`: `b(x + θ) = b(x) + 2θ`. By induction and with
   `a^-1`, `b(x + nθ) = b(x) + 2nθ` for all `n ∈ Z`.
3. For `k ∈ K` pick `n_j θ -> k`. By continuity of `b`, translation and
   `x ↦ 2x`, `b(x + k) = b(x) + 2k`. With `c = b(0)` this gives `b(x) = c + 2x`
   on `K`.
4. `b(-c) = c - 2c = -c`, so `y = -c` is fixed by `b`.
5. `a = t^-1 b t`, so `a(t^-1 y) = t^-1 b y = t^-1 y`. ∎

Step 4 uses `1 - 2 = -1`. For `BG_n` with `n ≥ 3`, a fixed point of `c + nx`
needs `(n-1)x = -c` to be solvable in `K`, and that can fail, e.g. on `Z_3` with
`n = 4`. So the claim is stated only for `BG = BG_2`.

**Corollaries.**
- **(O1)** No action of `BG` on a compact metrizable space with at least two
  points has `a` acting minimally and equicontinuously: `a` would have a fixed
  point while being minimal.
- **(O2)** `BS(1,2)` has a self-similar affine model on the ternary tree:
  `Z_3 ⊇ Z[1/2]`, with `a: x ↦ x + 1` and `b: x ↦ 2x`.
  - State-closure: if `x ∈ Z[1/2]` and `x ≡ d (mod 3Z_3)` with `d ∈ {0,1,2}`,
    then `(x - d)/3 ∈ Z[1/2]`, because `3 ∤ 2^j`.
  - No extension: this model and every odometer model of `BS(1,2)` extend to
    no action of `BG` on the same space, by (O1).
  - Hosts: in particular, no embedding of `BG` into a Röver–Nekrashevych group
    `V_3(H) ⊇ BS(1,2)` can send `a` to the adding machine.
- **(O3)** The projective 2-adic similarity model of `BS(1,2)` also fails.
  - The model: `P^1(Q_2) = Q_2 ∪ {∞}`, `a: x ↦ x + 1`, `b: x ↦ 2x`. Check:
    `b a b^-1 (x) = 2(x/2 + 1) = x + 2 = a^2(x)`.
  - Fixed points: `Fix(a) = {∞}`, while `Fix(b) = {0, ∞}`.
  - Obstruction: `b` is conjugate to `a` in `BG`, so `|Fix(a)| = |Fix(b)|` in
    every action. Hence this model extends to no `BG`-action either.

## 3. Host classes for `BG`: status

| Host class | Status for `BG` | Where |
|---|---|---|
| Bux–Llosa Isenrich–Wu tree hosts over virtually free, abelian or nilpotent vertex groups | dead | `baumslag-gersten-base-is-elliptic-in-every-tree-action` |
| Linear groups over any field (char-p Leavitt tensor hosts, char-0 root) | dead | §1 (L) |
| Subgroups of `Aut(T_d)`; fp self-similar hosts (Zaremsky Thm 1.1) | dead | §1 (S) |
| Odometer and affine `Z_p` models of `BS(1,2)`, projective 2-adic model | dead | §2 (O1)–(O3) |
| Röver–Nekrashevych `V_d(H)` and eventually-similar hosts | **open** | §4 |
| Rational similarity groups (BBMZ arXiv:2309.06224) | **open** | §5 |
| Type (A) / twisted Brin–Thompson hosts (Zaremsky arXiv:2405.18354; FFWZ) | **open** | §5 |

## 4. The FW obstructions do not apply

`t ↦ 1, a ↦ 0` defines a surjection `BG -> Z` (the relator has `t`-exponent
sum `0`). So `BG` acts on the simplicial line without a global fixed point.
Therefore `BG` has neither property FW nor property (T).

`fw-subgroups-of-eventually-similar-groups-virtually-embed` and
`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` only constrain FW
(respectively Kazhdan) subgroups, so they say nothing about `BG`. Röver–Nekrashevych
and eventually-similar hosts remain possible.

The lane directive assumed that "RN hosts are out, by the (T) obstruction".
That is false for `BG`: those groups contain `V`, which is not residually
finite, so residual finiteness does not exclude them either.

Inside `V_d(H)`, §2 excludes the simplest attempt: sending `a` to an adding
machine on the whole Cantor space. More generally, if `a` acts as an odometer on
an `⟨a,b⟩`-invariant piece, then `a` must fix some point outside that piece.

## 5. What an embedding would need

- **Dynamics of `a`.** In any action of `BG`, `Fix(b) = t Fix(a)`, so the two
  fixed sets are homeomorphic (§2 O3). If `a` has an equicontinuous minimal
  piece that `b` preserves, then `a` has a fixed point (§2).
  The chain `a_i = t^i a t^-i` (so `a_0 = a`, `a_1 = b`) satisfies
  `a_i a_(i-1) a_i^-1 = a_(i-1)^2`, and all the `a_i` are conjugate. The
  kernel of `BG -> Z` is the infinite amalgam
  `... *_Z BS(1,2) *_Z BS(1,2) *_Z ...` along this chain, and `t` acts as the
  shift.
- **Rational similarity groups.** BBMZ prove that every hyperbolic group embeds
  in a full, contracting RSG. The proof uses the group `[[ G | ∂_h G ]]`, which
  comes from the action of `G` on its horofunction boundary `∂_h G`. `BG`
  contains `BS(1,2)`, so it is not hyperbolic. An RSG host for `BG` would need
  some other compact model, and none is known here.
- **Type (A) actions.** By Zaremsky's Theorem A (arXiv:2405.18354), `SV_G` is
  finitely presented if and only if the action of `G` on `S` is of type (A):
  - the action is faithful;
  - `G` is finitely presented;
  - every point stabilizer is finitely generated;
  - there are finitely many `G`-orbits of two-element subsets.

  Every subgroup of such a `G` satisfies Boone–Higman. The obvious candidate is
  `G = BG` acting on the vertices of the Bass–Serre tree of the HNN structure.
  Its stabilizers are conjugates of `BS(1,2)` and are finitely generated. But
  tree distance is an invariant of vertex pairs and is unbounded, so there are
  infinitely many orbits of two-element subsets. Not attempted further.

## 6. Sources and checks

- §1 and §2 are self-contained. They use only Malcev's theorem (standard) and
  the structure of minimal equicontinuous homeomorphisms (standard).
- Checked from source on 2026-09-12, using copies on MSI left by earlier lanes:
  - **Zaremsky, arXiv:2405.09722.** Extracted PDF text,
    `/scratch.global/sauer354/bh-reviewer/2405.09722.txt`, lines 29–30.
    Theorem 1.1: "Every finitely presented self-similar group embeds in a
    finitely presented simple group, and hence satisfies the Boone–Higman
    conjecture."
  - **BBMZ, arXiv:2309.06224.** TeX source,
    `/scratch.global/sauer354/bh-rsg/src-2309.06224/hyperbolic_boone_higman.tex`.
    Title at line 97. The abstract at line 126 says every hyperbolic group
    embeds in a full, contracting RSG. Line 202 gives the horofunction boundary
    `∂_h G`.
  - **Zaremsky, arXiv:2405.18354v2.** Page 1 of the PDF,
    `/scratch.global/sauer354/bh-type-a/2405.18354.pdf`: the definition of
    type (A) and Theorem A.
  - **FFWZ.** Fournier-Facio–Wu–Zaremsky, *Abstract twisted Brin–Thompson
    groups*, arXiv:2603.24687. Checked against the title page of the extracted
    text in `bh-reviewer/`.
- Before the check, §5 said "Gromov boundary" and "finitely presented
  stabilizers". The sources show the horofunction boundary and finitely
  generated stabilizers.
- No novelty claimed: §1 is Baumslag 1969 in a standard form. §2 is
  elementary and very likely folklore.
