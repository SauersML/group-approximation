# gq-explicit-fp — Problem 2.7 (G'): explicit NATURAL f.p. group containing GL_n(Q)

## Approach
- Family: reframing + obstruction. Signature: "natural host classes for Problem 2.7".
- Dropped my piece-group lemma: gq-solenoid lands the general form (piecewise-commutative-linear-hosts-miss-linear-gl-n-q).

## Established
- 0d3e63f70: root `gl-n-q-explicit-natural-fp-overgroup` (OPEN): sources (survey Problem 2.7, Kourovka 14.10(c) via
  Mikaelian's quote), known cases, necessary host features (non-RF; element conjugate to all its powers and divisible;
  n>=3: SL_3(Z) forbids a-T-menable hosts), host-class status table, and a germ-at-infinity argument that
  Aff(Q), GL_n(Q) (n>=2), SL_2(Q) are not in Brin's A / Aut(F) (independent of Burillo-Felipe; Brin's description
  of A not re-read at source).

## Needs
- Someone to check Brin 1996 (Publ. IHES 84) description of A: PL dyadic, discrete breakpoints, periodic near +-inf.
- Kourovka v46 entry 14.10 text and comments (status of (c)).

## Dead
- Brin's A / Aut(F) as host for Aff(Q) and up (germ argument, see node Attempts 1).

## Sparks (not pursuing)
- Abstract commensurators: GL_n(Q) = Comm(Z^n); test Comm(G) for f.p. G containing Z^n rigidly (e.g. Comm(F), Burillo-Cleary-Rover).
- E_N(L) for Leavitt-type rings over a f.p. ring containing Q.
- nV for n>=3: first test SL_3(Z) <= nV.
