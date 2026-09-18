# Wave swarm-0917, orchestrator B: lane record

`lanes.json` is the raw result of the 28 lanes on the goals
`fpbs-fixed-price-universal` and `fpbs-benjamini-schramm-universal`. Each lane
has a worker report, three referee verdicts and a landing outcome.
`swarm-lanes.js` is the workflow script: worker, then three referee lenses,
then a land agent.

All research content these lanes produced is on main. The last of it landed in
7246ce77e: three restored Attempts entries and the zero-free connection
polynomial route, which is kept OPEN. This branch keeps the process record
only. Unrefereed or refuted lane claims remain OPEN in the graph.

Still open for a later wave:
- the five lanes that hit usage limits: t-cyctail, t-resid, t-genmove,
  t-fp1kern and t-pivot;
- full re-referees of d-fp-heretic (1e4619de3) and d-fp-transplant
  (020196184), which each lost one referee vote.
