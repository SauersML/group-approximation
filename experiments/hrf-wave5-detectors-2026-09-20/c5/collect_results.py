"""Assemble complete25-pair exact rank records and check every H1 identity."""
from pathlib import Path
import json
base=Path(__file__).parent
initial=base/'tensor_initial_result.json'
if not initial.exists():
 initial.write_text((base/'tensor_homology_result.json').read_text())
results={}
for path in [initial]+sorted(base.glob('tensor_pair_*_*.json')):
 for row in json.loads(path.read_text()):
  key=tuple(row['summands'])
  if key in results: assert results[key]==row
  results[key]=row
assert set(results)=={(i,j) for i in range(5) for j in range(5)}
mods=json.loads((base/'projective_summands.json').read_text())
isos=json.loads((base/'isomorphisms.json').read_text())
reps=sorted({c['representative'] for c in isos}); dims=[len(mods[r]['basis']) for r in reps]
for (i,j),row in results.items():
 assert row['dimension']==dims[i]*dims[j]
 assert row['h1']==sum(row['pair_ranks'])-row['triple_rank']-sum(row['edge_dimensions'])+row['global_fixed']==0
for path in base.glob('tensor_stage_*.json'):
 row=json.loads(path.read_text()); target=results[tuple(row['summands'])]
 for key in ['dimension','edge_dimensions','global_fixed']: assert row[key]==target[key]
 stage=row['stage']
 expected=target['triple_rank'] if stage=='triple' else target['edge_dimensions'][int(stage[-1])] if stage.startswith('edge') else target['pair_ranks'][['pair01','pair02','pair12'].index(stage)]
 assert row['rank']==expected
full=[results[key] for key in sorted(results)]
(base/'tensor_homology_result.json').write_text(json.dumps(full,indent=2)+'\n')
print('ALL25_TENSOR_IDENTITIES_PASS',dims)
