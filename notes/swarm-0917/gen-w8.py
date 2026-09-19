import json,re
S='/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad'
J='/root/.claude/projects/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/subagents/workflows/wf_615b3898-6a5/journal.jsonl'
a=json.load(open(S+'/w7-args.json'))
lab={};work={}
for l in open(J):
  d=json.loads(l)
  if d.get('type')=='started': lab[d['agentId']]=d['label']
  r=d.get('result')
  if isinstance(r,dict) and lab[d['agentId']].startswith('work:'): work[lab[d['agentId']][5:]]=r
goal={l['key']:l['goal'] for l in a['lanes']}
lanes=[]
for l in a['lanes']:
  k=l['key']; s=k.split('-')[1]; kind=k.split('-',2)[2]
  n=dict(l); n['key']='w8-'+s+'-'+kind
  if kind=='follow':
    g=l['goal']
    notes=[]
    for wk,r in work.items():
      if goal.get(wk)!=g: continue
      notes.append(f"[{wk}] target {r.get('id')} ({r.get('status')}); established {r.get('established')}. What is left: {str(r.get('impact',''))[:700]}")
    if not notes: continue
    n['text']=(f"FOLLOW-THROUGH toward {g}. Wave 7 of this swarm (landed on main in the last 4 hours) reported the following; each note says what it proved and what is left:\n"+"\n".join(notes)+
      f"\nPick the single most promising 'what is left' step above that would move {g} closest to ESTABLISHED (prefer a step that closes a route's last hole, or a strong counterexample that redirects the program), check `bin/cairn context` on it and git log origin/main --since=4.hours for anyone who already took it, and attack it for the full statement. Do not attempt narrow special cases.")
  elif 'text' in n:
    n['text']=n['text'].replace('waves 5 and 6','waves 6 and 7')
  lanes.append(n)
a['lanes']=lanes; a['prefix']='swarm-0917-w8'; a['maxWorkers']=20
json.dump(a,open(S+'/w8-args.json','w'))
js=open(S+'/swarm-w7.js').read()
m=re.search(r'const W6 = (.*?)\nconst REFEREE',js,re.S)
js=js[:m.start(1)]+json.dumps(a)+js[m.end(1):]
js=js.replace("'swarm-0917-w7'","'swarm-0917-w8'")
open(S+'/swarm-w8.js','w').write(js)
print(len(lanes), sum(1 for x in lanes if x['key'].endswith('follow')))
