"""Generate proposed module-isomorphism certificates to avoid duplicate pairs."""
from pathlib import Path
import json
base=Path(__file__).parent
mods=json.loads((base/'projective_summands.json').read_text()); data=json.loads((base/'module_input.json').read_text()); p=data['prime']
s='matrices := '+str([m['generators'] for m in mods])+';;\n'
s+='mods := List(matrices, mm->GModuleByMats(List(mm,m->m*One(GF('+str(p)+'))),GF('+str(p)+')));;\n'
s+='reps := [];; certificates := [];;\nfor n in [1..Length(mods)] do\n found := false;\n for r in reps do\n  if MTX.Dimension(mods[n])=MTX.Dimension(mods[r]) then\n   T := MTX.IsomorphismModules(mods[n],mods[r]);\n   if T<>fail then Add(certificates,[r,T]); found:=true; break; fi;\n  fi;\n od;\n if not found then Add(reps,n); Add(certificates,[n,IdentityMat(MTX.Dimension(mods[n]),GF('+str(p)+'))]); fi;\nod;\n'
s+='Print("REPRESENTATIVES ",reps,"\\n");\n'
s+='out := OutputTextFile("'+str((base/'isomorphisms.json').resolve())+'",false);; PrintTo(out,"[\\n");;\n'
s+='for n in [1..Length(certificates)] do c:=certificates[n]; PrintTo(out,"{\\"representative\\":",c[1]-1,",\\"map\\":",List(c[2],r->List(r,IntFFE)),"}"); if n<Length(certificates) then PrintTo(out,",\\n"); fi; od; PrintTo(out,"\\n]\\n");; CloseStream(out);; QUIT;\n'
(base/'isomorphisms.g').write_text(s)
