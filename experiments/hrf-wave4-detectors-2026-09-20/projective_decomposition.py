"""Generate exact GAP input from the independently audited coset construction."""
from pathlib import Path
base=Path(__file__).parent
namespace={}
source=(base/'borel_a4_homology.py').read_text().split('\nvs=')[0]
exec(compile(source,'audited_borel_a4_construction','exec'),namespace)
ns=namespace
matrices=ns['xs']+[ns['y']]
permutations=[[ns['labels'][ns['mul'](x,g)]+1 for g in ns['representatives']] for x in matrices]
script='perms := '+str(permutations)+';;\n'
script+='gens := List(perms, p->PermutationMat(PermList(p),285,GF(5)));;\n'
script+='modu := GModuleByMats(gens,GF(5));;\n'
script+='decomp := MTX.Indecomposition(modu);;\n'
script+='Print("DIMENSIONS ",List(decomp,d->MTX.Dimension(d[2])),"\\n");\n'
script+='out := OutputTextFile("'+str((base/'projective_summands.json').resolve())+'",false);;\n'
script+='PrintTo(out,"[\\n");;\n'
script+='for n in [1..Length(decomp)] do\n'
script+=' d := decomp[n];\n'
script+=' PrintTo(out,"{\\"basis\\":",List(d[1],r->List(r,IntFFE)),",\\"generators\\":",List(MTX.Generators(d[2]),m->List(m,r->List(r,IntFFE))),"}");\n'
script+=' if n<Length(decomp) then PrintTo(out,",\\n"); fi;\n'
script+='od;\nPrintTo(out,"\\n]\\n");; CloseStream(out);; QUIT;\n'
(base/'decompose.g').write_text(script)
