import json, os, sys
# usage: replay.py OUTROOT TAG PREFIX[,PREFIX2] TRANSCRIPT...
out, tag, prefixes = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
for tr in sys.argv[4:]:
    uses, errs = [], set()
    bash_creates = []
    with open(tr) as fh:
        for line in fh:
            try:
                d = json.loads(line)
            except Exception:
                continue
            c = d.get('message', {}).get('content')
            if not isinstance(c, list):
                continue
            for x in c:
                if x.get('type') == 'tool_use' and x.get('name') in ('Write', 'Edit'):
                    uses.append(x)
                elif x.get('type') == 'tool_use' and x.get('name') == 'Bash':
                    cmd = x.get('input', {}).get('command', '')
                    if any(p in cmd for p in prefixes) and ('mv ' in cmd or 'cp ' in cmd or '> ' in cmd):
                        bash_creates.append(cmd[:300].replace('\n', ' | '))
                elif x.get('type') == 'tool_result' and x.get('is_error'):
                    errs.add(x.get('tool_use_id'))
    files, status = {}, {}
    for u in uses:
        if u.get('id') in errs:
            continue
        inp = u.get('input', {})
        p = inp.get('file_path', '')
        if not any(p.startswith(q) for q in prefixes):
            continue
        if u['name'] == 'Write':
            files[p] = inp.get('content', '')
            status[p] = 'WRITE'
        else:
            if p not in files:
                status[p] = 'EDIT-NO-BASE'
                continue
            old, new = inp.get('old_string', ''), inp.get('new_string', '')
            if old not in files[p]:
                status[p] = 'EDIT-MISS'
                continue
            files[p] = files[p].replace(old, new) if inp.get('replace_all') else files[p].replace(old, new, 1)
    name = os.path.basename(tr).replace('.jsonl', '')
    for p, s in status.items():
        if p in files:
            dest = os.path.join(out, tag, name, p.lstrip('/'))
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, 'w') as fh:
                fh.write(files[p])
        print(tag, name, s, p)
    for b in bash_creates[-12:]:
        print(tag, name, 'BASH', b)
