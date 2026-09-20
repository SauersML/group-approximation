"""Reconstruct actual group/coset actions independently of stored module JSON."""
from pathlib import Path
import json

def verify(data):
 base=Path(__file__).parent; ns={}
 src=base.parent.parent/'hrf-wave4-detectors-2026-09-20/borel_a4_homology.py'
 exec(compile(src.read_text().split('\nvs=')[0],'audited_cosets','exec'),ns)
 G=ns['G']; mul=ns['mul']; C=sorted(ns['generate']([ns['xs'][0]]))
 labels={}; reps=[]
 for g in G:
  if g in labels: continue
  for c in C: labels[mul(g,c)]=len(reps)
  reps.append(g)
 assert data['prime']==3 and len(C)==5 and len(G)==3420 and len(reps)==684
 assert data['group']==[list(g) for g in G]
 assert data['subgroup']==[list(g) for g in C]
 assert data['representatives']==[list(g) for g in reps]
 assert data['labels']==[labels[g] for g in G]
 assert data['generators']==[list(g) for g in ns['xs'][:2]]
 assert data['permutations']==[[labels[mul(x,g)] for g in reps] for x in ns['xs']+[ns['y']]]
 return True

if __name__=='__main__':
 verify(json.loads(Path(__file__).with_name('module_input.json').read_text()))
 print('FULL_GROUP_AND_COSET_INPUT_PASS')
