Simulation of the dead weighted-surface continuity route (swarm-0917, 2026-09-18)
===============================================================================

Question: could fpbs-dead-weighted-surface-continuity-l2 make cairn derive the
flagship fpbs-benjamini-schramm-universal ESTABLISHED, even though that route's
own body says it is dead?

Setup: copy research/, tools/, bin/ and experiments/ into a scratch directory
SIM. Every command below runs as
  CAIRN_ROOT=SIM python3 SIM/tools/cairn.py why <id>

Run A: force both requirements true
  Add two route files, each with `requires: []`:
    target fpbs-sprinkling-lemma-referee-confirmation
    target fpbs-uniform-floor-equivalence-restricted-to-monotone-paths
  Result:
    fpbs-critical-dyadic-projection-estimate          OPEN
    fpbs-dead-weighted-surface-continuity-l2          INVALIDATED
                                                      (invalidated by fpbs-weighted-surface-continuity-reduces-to-uniform-floor)
    fpbs-benjamini-schramm-universal                  OPEN
  The invalidator becomes established at the same moment as the dead route's
  requirements, because its only route has the same two requirements.

Run B: Run A, plus refute the reduction claim
  Add `refuted_by: [sim-every-path-form-false]` to
  fpbs-weighted-surface-continuity-reduces-to-uniform-floor, plus an
  established claim sim-every-path-form-false with a direct-proof route.
  This models the every-path statement being proved false, which item 1 of
  fpbs-uniform-floor-equivalence-restricted-to-monotone-paths already records
  on F_4 x Z.
  Result:
    fpbs-benjamini-schramm-universal  [ESTABLISHED via fpbs-universal-dyadic-route]
  The only signal is one "contradiction" error on the reduction claim, among
  the hundreds of pre-existing lint errors from other lanes.

Fix: fpbs-continuity-route-needs-floor-premise has a direct proof, depends on
neither requirement, and invalidates the dead route. Adding it to Run B leaves
the flagship OPEN.
