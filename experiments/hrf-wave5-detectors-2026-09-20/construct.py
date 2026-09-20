"""PSL19 coefficient-three projective module on cosets of N_Q(C5)."""
from pathlib import Path
import json
base=Path(__file__).parent
ns={}
exec(compile((base.parent/'hrf-wave4-detectors-2026-09-20/borel_a4_homology.py').read_text().split('\nvs=')[0],'audited_cosets','exec'),ns)
G=ns['G']; mul=ns['mul']; inv=ns['inv']; x=ns['xs'][0]; C=set(ns['generate']([x]))
A=[g for g in G if mul(mul(inv(g),x),g) in C]; assert len(A)==20
labels={}; reps=[]
for g in G:
 if g in labels: continue
 for a in A: labels[mul(g,a)]=len(reps)
 reps.append(g)
assert len(reps)==171
perms=[[labels[mul(x,g)] for g in reps] for x in ns['xs']+[ns['y']]]
data={'prime':3,'group':G,'subgroup':A,'representatives':reps,'permutations':perms,'labels':[labels[g] for g in G],'generators':ns['xs'][:2]}
(base/'module_input.json').write_text(json.dumps(data)+'\n')
script='perms := '+str([[a+1 for a in row] for row in perms])+';;\n'
script+='gens := List(perms, p->PermutationMat(PermList(p),171,GF(3)));;\n'
script+='modu := GModuleByMats(gens,GF(3));; decomp := MTX.Indecomposition(modu);;\n'
script+='Print("DIMENSIONS ",List(decomp,d->MTX.Dimension(d[2])),"\\n");\n'
script+='out := OutputTextFile("'+str((base/'projective_summands.json').resolve())+'",false);; PrintTo(out,"[\\n");;\n'
script+='for n in [1..Length(decomp)] do d := decomp[n];\n'
script+='PrintTo(out,"{\\"basis\\":",List(d[1],r->List(r,IntFFE)),",\\"generators\\":",List(MTX.Generators(d[2]),m->List(m,r->List(r,IntFFE))),"}");\n'
script+='if n<Length(decomp) then PrintTo(out,",\\n"); fi; od;\nPrintTo(out,"\\n]\\n");; CloseStream(out);; QUIT;\n'
(base/'decompose.g').write_text(script)
