#!/usr/bin/env python3
"""Assemble the self-contained web edition of non_mf_groups_exist.tex.

The page embeds the raw TeX and the claims manifest verbatim; a client-side
renderer (parser.js + ui.js) typesets them with an inlined KaTeX, so the
manuscript stays the single source of truth and the site follows every tex
push with no separate content pipeline.  Stdlib only; no toolchain.

    python3 tools/paper_site/build.py --out .cairn/site/paper/index.html
"""
import argparse
import base64
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def read(p):
    return Path(p).read_text(encoding='utf-8')


DECL_HEAD = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)', re.M)


def extract_decl(module, decl):
    """Best-effort: the statement of `decl` from <module>.lean, up to its `:=`."""
    path = REPO / 'GroupApproximation' / (module + '.lean')
    if not path.exists():
        path = REPO / (module + '.lean')
    if not path.exists():
        return None
    src = path.read_text(encoding='utf-8')
    name = decl.split('.')[-1]
    for m in DECL_HEAD.finditer(src):
        if m.group(2) == name:
            tail = src[m.start(1):]
            stop = re.search(r':=|\n\n\n', tail)
            code = tail[:stop.start()].rstrip() if stop else tail
            lines = code.splitlines()
            if len(lines) > 40:
                code = '\n'.join(lines[:40]) + '\n  …'
            return code[:4000]
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=str(HERE / 'index.html'))
    args = ap.parse_args()

    katex_css = read(HERE / 'katex' / 'katex.min.css')
    katex_js = read(HERE / 'katex' / 'katex.min.js')
    site_css = read(HERE / 'styles.css')
    parser_js = read(HERE / 'parser.js')
    ui_js = read(HERE / 'ui.js')
    template = read(HERE / 'template.html')
    tex = read(REPO / 'non_mf_groups_exist.tex')
    claims = read(REPO / 'docs' / 'NON_MF_NUMBERED_CLAIMS.json')

    # inline the woff2 fonts into the KaTeX css; drop the woff/ttf fallbacks
    def font_uri(m):
        data = (HERE / 'katex' / 'fonts' / f'{m.group(1)}.woff2').read_bytes()
        return 'url(data:font/woff2;base64,%s) format("woff2")' % base64.b64encode(data).decode('ascii')

    katex_css = re.sub(r'url\(fonts/([A-Za-z0-9_-]+)\.woff2\) format\("woff2"\)', font_uri, katex_css)
    katex_css = re.sub(r',url\(fonts/[A-Za-z0-9_-]+\.(?:woff|ttf)\) format\("(?:woff|truetype)"\)', '', katex_css)
    leftovers = re.findall(r'url\(fonts/[^)]*\)', katex_css)
    if leftovers:
        sys.exit(f'unresolved font urls remain: {leftovers[:4]}')

    lean_src = {}
    for c in json.loads(claims)['claims']:
        for l in c.get('lean', []):
            key = l['module'] + '|' + l['declaration']
            if key not in lean_src:
                code = extract_decl(l['module'], l['declaration'])
                if code:
                    lean_src[key] = code
    data_js = (
        'window.PAPER_TEX = ' + json.dumps(tex).replace('</', '<\\/') + ';\n'
        'window.CLAIMS = ' + json.dumps(json.loads(claims)).replace('</', '<\\/') + ';\n'
        'window.LEAN_SRC = ' + json.dumps(lean_src).replace('</', '<\\/') + ';\n'
    )

    for name, payload in [
        ('KATEX_JS', katex_js), ('PARSER_JS', parser_js), ('UI_JS', ui_js), ('DATA_JS', data_js),
    ]:
        if '</script' in payload.replace('<\\/script', ''):
            sys.exit(f'{name} contains a literal </script sequence')

    out = template
    for name, payload in [
        ('KATEX_CSS', katex_css), ('SITE_CSS', site_css),
        ('KATEX_JS', katex_js), ('DATA_JS', data_js),
        ('PARSER_JS', parser_js), ('UI_JS', ui_js),
    ]:
        marker = f'/*__{name}__*/'
        assert marker in out, marker
        out = out.replace(marker, payload)

    dest = Path(args.out)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(out, encoding='utf-8')
    print(f'wrote {dest} ({len(out)/1e6:.2f} MB)')


if __name__ == '__main__':
    main()
