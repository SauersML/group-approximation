---
rg: 2
id: two-species-bilateral-mapping-torus-hosts
kind: claim
title: Bilaterally separating V observations realize mapping tori and twisted V lamps in two-species compact-core hosts
distinct_from:
  dynamically-v-separated-groups-satisfy-boone-higman: that embeds the observed group using a one-sided injective endomorphism; this constructs an exact bilateral mapping-torus bridge and a larger restricted lamp extension.
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

**OPEN — explicit construction and input-verification lemma; independent review pending.**

Let `D` have type `F_k`, `k≥2` or `∞`, let `φ∈Aut(D)`, and let
`ρ:D→V` satisfy both `⋂_{j≥0}ker(ρφ^j)=1` and
`⋂_{j≥0}ker(ρφ^{-j})=1`. The two-species full group `Γ(D,φ,ρ)` of
artifact §§4–5 is well defined in every finite forest and satisfies
all hypotheses of `compact-core-singfix-finiteness`, with local profile
`L=D`, depth-zero base isotropy `H=1`, and advances `φ,φ^-1` on the
eventually-zero and eventually-one species respectively.

It contains the mapping torus `T=<D,t | t^-1gt=φ(g)>`, faithfully
realized by the integer-shell profiles and shift, and contains the
larger faithful semidirect product `V^(Z)⋊T` with action
`t e_n(v)t^-1=e_{n+1}(v)` and
`g e_n(v)g^-1=e_n(ρ(φ^n(g))vρ(φ^n(g))^-1)`.

## Attempts

Use the distinct `V`-orbits of eventually-zero and eventually-one
points, with forward and backward observation profiles. Tail
separation follows from the automorphism and the two kernel conditions.
Chart shifts apply iterates of `φ` and preserve the profile families.
Supported profile cutoffs and zooms are proposed to isolate each germ;
these must be checked along with fullness and all finite-forest data.

The prefix shift `0w→00w,10w→01w,11w→1w` moves shell `n` to `n+1`.
The proposed profile on shell `n` is `ρφ^n(g)`, giving the exact
relation `X^-1 ĝ X=widehat{φ(g)}` including the bridge. Shell
displacement detects the stable-letter exponent; tail separation
detects a profile even modulo finitely supported `V` lamps. Artifact
§§4–5 gives the full injection argument and outstanding membership
checks. Two same-species endpoints in different roots would not justify
this construction, since chart transport could mix both profile families.
