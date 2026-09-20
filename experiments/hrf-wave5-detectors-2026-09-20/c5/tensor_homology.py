"""Full projective-tensor H1 for characteristic3, with exact C5 splitting."""
import json,time,argparse
from pathlib import Path
import numpy as np
from flint import nmod_mat
base=Path(__file__).parent; data=json.loads((base/'module_input.json').read_text()); p=data['prime']
from verify_input import verify
assert verify(data)
mods=json.loads((base/'projective_summands.json').read_text()); n=len(data['representatives'])
def rank(rows): return nmod_mat(rows,p).rank() if len(rows) else 0
def independent(rows):
 R,r=nmod_mat(rows,p).rref()
 return np.array([[int(R[i,j]) for j in range(R.ncols())] for i in range(r)],dtype=np.int64)
assert rank(sum([m['basis'] for m in mods],[]))==n
for m in mods:
 B=np.array(m['basis'],dtype=np.int64)
 for g,perm in zip(m['generators'],data['permutations']):
  assert np.array_equal(np.array(g)@B%p,B[:,np.argsort(perm)])
print('SUMMAND_CERTIFICATE_PASS',flush=True)
isos=json.loads((base/'isomorphisms.json').read_text())
assert len(isos)==len(mods)
for i,c in enumerate(isos):
 r=c['representative']; T=np.array(c['map'],dtype=np.int64)
 di=len(mods[i]['basis']); dr=len(mods[r]['basis'])
 assert di==dr and T.shape==(di,dr)
 assert rank(T.tolist())==di
 for a,b in zip(mods[i]['generators'],mods[r]['generators']):
  assert np.array_equal(np.array(a)@T%p,T@np.array(b)%p)
representatives=sorted({c['representative'] for c in isos})
mods=[mods[r] for r in representatives]
print('ISOMORPHISM_CERTIFICATES_PASS',representatives,flush=True)

def c5_blocks(g):
 g=np.array(g,dtype=np.int64); a=len(g); eye=np.eye(a,dtype=np.int64)
 powers=[eye]
 for k in range(5): powers.append(powers[-1]@g%p)
 assert np.array_equal(powers[5],eye)
 S=sum(powers[:5])*pow(5,-1,p)%p
 fixed=independent(S.tolist()); U=(eye-S)%p
 blocks=[]; basis=fixed.tolist()
 for v in U:
  string=[v]
  for k in range(4): string.append(string[-1]@g%p)
  candidate=basis+[z.tolist() for z in string[:4]]
  r=rank(candidate)
  if r>len(basis):
   assert r==len(basis)+4
   assert not np.any(sum(string)%p)
   blocks.append(np.array(string)); basis=candidate
  if len(basis)==a: break
 assert len(basis)==a and rank(basis)==a
 return fixed,blocks
for m in mods:
 m['blocks']=[c5_blocks(g) for g in m['generators']]
 d=len(m['basis']); eye=np.eye(d,dtype=np.int64)
 m['fixed']=d-rank(np.concatenate([(np.array(g)-eye).T%p for g in m['generators']]).tolist())

def edge_fixed(A,B):
 fa,ba=A; fb,bb=B; rows=[]
 for a in fa:
  for b in fb: rows.append(np.outer(a,b).ravel().tolist())
 for a in ba:
  for b in bb:
   for s in range(4): rows.append((sum(np.outer(a[k],b[(k+s)%5]) for k in range(5))%p).ravel().tolist())
 if args.rank_stage is None: assert rank(rows)==len(rows)
 return rows
parser=argparse.ArgumentParser(); parser.add_argument('--only',nargs=2,type=int)
parser.add_argument('--rank-stage',choices=['edge0','edge1','edge2','pair01','pair02','pair12','triple'])
args=parser.parse_args()
results=[]; start=time.time()
for i,A in enumerate(mods):
 for j,B in enumerate(mods):
  if args.only is not None and args.only!=[i,j]: continue
  d=len(A['basis'])*len(B['basis'])
  E=[edge_fixed(A['blocks'][a],B['blocks'][b]) for a,b in [(0,0),(1,1),(2,3)]]
  if args.rank_stage is not None:
   stage=args.rank_stage
   if stage.startswith('edge'): value=rank(E[int(stage[-1])])
   elif stage.startswith('pair'): value=rank(E[int(stage[-2])]+E[int(stage[-1])])
   else: value=rank(sum(E,[]))
   result={'summands':[i,j],'dimension':d,'edge_dimensions':list(map(len,E)),'global_fixed':A['fixed']*B['fixed'],'stage':stage,'rank':value}
   (base/('tensor_stage_%d_%d_%s.json'%(i,j,stage))).write_text(json.dumps(result,indent=2)+'\n')
   print(json.dumps(result),'seconds',round(time.time()-start,2),flush=True)
   continue
  pair=[rank(E[a]+E[b]) for a,b in [(0,1),(0,2),(1,2)]]
  total=rank(sum(E,[])); fixed=A['fixed']*B['fixed']
  h1=sum(pair)-total-sum(map(len,E))+fixed
  assert h1>=0
  result={'summands':[i,j],'dimension':d,'edge_dimensions':list(map(len,E)),'pair_ranks':pair,'triple_rank':total,'global_fixed':fixed,'h1':h1}
  results.append(result)
  output=base/('tensor_pair_%d_%d.json'%(i,j) if args.only is not None else 'tensor_homology_result.json')
  output.write_text(json.dumps(results,indent=2)+'\n')
  print(json.dumps(result),'seconds',round(time.time()-start,2),flush=True)
