"""Split Ind(C5,Q) through four F3 characters of D20/C5=V4."""
from pathlib import Path
import json
base=Path(__file__).parent
small=json.loads((base.parent/'module_input.json').read_text()); big=json.loads((base/'module_input.json').read_text())
G=[tuple(g) for g in big['group']]; inds={g:i for i,g in enumerate(G)}
C={tuple(g) for g in big['subgroup']}; D=[tuple(g) for g in small['subgroup']]
def mul(x,y):
 a,b,c,d=x; e,f,g,h=y
 m=tuple(t%19 for t in (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
 return min(m,tuple(-t%19 for t in m))
I=(1,0,0,1); quotient=[]; qlabel={}
for d in [I]+D:
 if d in qlabel: continue
 for c in C: qlabel[mul(d,c)]=len(quotient)
 quotient.append(d)
assert len(quotient)==4
r=quotient[1]; s=quotient[2]; reps=[I,r,s,mul(r,s)]
labels={mul(t,c):j for j,t in enumerate(reps) for c in C}
assert all(labels[mul(a,b)]==labels[a]^labels[b] for a in D for b in D)
parts=[]
for character in range(4):
 B=[[0]*684 for _ in range(171)]
 for row,g in enumerate(small['representatives']):
  for bits,t in enumerate(reps):
   j=big['labels'][inds[mul(g,t)]]
   B[row][j]=1 if (bits&character).bit_count()%2==0 else 2
 gens=[]
 for perm in big['permutations']:
  mat=[[0]*171 for _ in range(171)]
  for row,g in enumerate(small['representatives']):
   origin=big['labels'][inds[tuple(g)]]; col=perm[origin]
   target=small['labels'][inds[tuple(big['representatives'][col])]]
   mat[row][target]=B[target][col]
  gens.append(mat)
 parts.append({'basis':B,'generators':gens})
(base/'normalizer_characters.json').write_text(json.dumps(parts)+'\n')
s='parts := '+str([[m['basis'],m['generators']] for m in parts])+';;\n'
s+='out := OutputTextFile("'+str((base/'projective_summands.json').resolve())+'",false);; PrintTo(out,"[\\n");; first:=true;;\n'
s+='for z in [1..4] do part:=parts[z]; modu:=GModuleByMats(List(part[2],m->m*One(GF(3))),GF(3));; dec:=MTX.Indecomposition(modu);; Print("PART ",z," DIMENSIONS ",List(dec,d->MTX.Dimension(d[2])),"\\n");\n'
s+='for d in dec do B:=d[1]*(part[1]*One(GF(3))); if not first then PrintTo(out,",\\n"); fi; first:=false; PrintTo(out,"{\\"basis\\":",List(B,r->List(r,IntFFE)),",\\"generators\\":",List(MTX.Generators(d[2]),m->List(m,r->List(r,IntFFE))),"}"); od; od;\nPrintTo(out,"\\n]\\n");; CloseStream(out);; QUIT;\n'
(base/'split_decompose.g').write_text(s)
