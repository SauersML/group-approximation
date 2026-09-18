import json,re
S='/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad'
J='/root/.claude/projects/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/subagents/workflows/wf_85f9b222-dba/journal.jsonl'
a=json.load(open(S+'/w12-args.json'))
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
  n=dict(l); n['key']='w13-'+s+'-'+kind
  if kind=='follow':
    g=l['goal']
    notes=[]
    for wk,r in work.items():
      if goal.get(wk)!=g: continue
      notes.append(f"[{wk}] target {r.get('id')} ({r.get('status')}); established {r.get('established')}. What is left: {str(r.get('impact',''))[:700]}")
    if not notes: continue
    n['text']=(f"FOLLOW-THROUGH toward {g}. Wave 12 of this swarm reported the following; each note says what it proved and what is left:\n"+"\n".join(notes)+
      f"\nPick the single most promising 'what is left' step above that would move {g} closest to ESTABLISHED (prefer a step that closes a route's last hole, or a strong counterexample that redirects the program), check `bin/cairn context` on it and git log --since=4.hours (your worktree starts from the swarm branch, which carries wave 12's results; main is failing its graph check because of another session's files, so most wave 10-12 results are not on origin/main yet) for anyone who already took it, and attack it for the full statement. Do not attempt narrow special cases.")
  elif 'text' in n:
    n['text']=n['text'].replace('waves 10 and 11','waves 11 and 12')
  lanes.append(n)
a['lanes']=lanes; a['prefix']='swarm-0917-w13'; a['maxWorkers']=20
json.dump(a,open(S+'/w13-args.json','w'))
js=open(S+'/swarm-w12.js').read()
m=re.search(r'const W6 = (.*?)\nconst REFEREE',js,re.S)
js=js[:m.start(1)]+json.dumps(a)+js[m.end(1):]
js=js.replace("'swarm-0917-w12'","'swarm-0917-w13'")
open(S+'/swarm-w13.js',"w").write(js)
print(len(lanes), sum(1 for x in lanes if x['key'].endswith('follow')))
