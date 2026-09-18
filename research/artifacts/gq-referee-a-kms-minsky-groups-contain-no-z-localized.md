# Referee report (gq-referee-a, proof-gap lens): KMS Minsky groups contain no Z_(l)

**Reviewed:** `kms-minsky-groups-contain-no-z-localized` and its route `-proof` (lane gq-infinite-primes, a1c262c67),
read on origin/main.

**Verdict: PASS.** No gaps found. The single import is KMS Theorem 4.3(a), quoted from the e-print. Checking that quote
belongs to the citation lens.

## The general lemma
- **Setup.** `N` has finite exponent `d`, and `S` is torsion-free.
- **Trivial intersection.** Every element of `S ∩ N` has finite order, so `S ∩ N = 1`, and `S` embeds in `G/N`.
- **Conclusion.** `G/N` is a finitely generated abelian group. Its subgroups are finitely generated, and the
  torsion-free ones are free abelian of finite rank. So `S` is free abelian of finite rank.

## The application
- **Variety product convention.** The product of varieties is the class of extensions: `𝒰𝒱 = {G : ∃ N ⊴ G, N ∈ 𝒰,
  G/N ∈ 𝒱}`. So `G(M) ∈ 𝒜_p^2 𝒜` gives a normal subgroup `N ∈ 𝒜_p^2`, which has exponent dividing `p^2`, with
  `G(M)/N` abelian.
- **Both readings work.** Reading `𝒜_p^2` as abelian of exponent `p^2` gives the same conclusion, as the proof notes.
  `G(M)` is finitely generated.
- **The excluded subgroups.**
  - `Z[1/q]` is not finitely generated.
  - `Z_(l)` contains `Z[1/q]` for every prime `q ≠ l`. `Z[1/P]` with `P ≠ ∅` contains `Z[1/q]` for `q ∈ P`. `(Q,+)`
    contains every `Z[1/q]`.
  - `G_l ⊇ Z_(l) f_0`.
  - So none of these embeds in any `G(M)`.

## Scope
- The reading of the bottleneck is correctly limited. The KMS finitely presented residually finite groups are
  torsion-by-abelian, so they cannot host `Z_(l)`. This closes route (a) for these specific groups only.
- The remark that Theorem 4.17 uses finite exponent of `T` is descriptive, and was not re-checked here.
