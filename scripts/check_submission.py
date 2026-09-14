"""Validate the selected source snapshot before kernel verification."""
from pathlib import Path
import json
import re
import subprocess
import sys
import tomllib
import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
CONFIG = 'Palomar/comparator-stw-xxii.json'
ROOTS = ['Palomar.STWProblemXXIIChallenge', 'Palomar.STWProblemXXIISolution',
         'Palomar.STWProblemXXIIModelTests']


def code(text):
    """Mask nested Lean comments and strings, retaining line boundaries."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        start = i
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if text[j] != '\n':
                out[j] = ' '
    assert depth == 0 and not string, 'Unterminated comment or string'
    return ''.join(out)


def main():
    metadata = yaml.safe_load((ROOT / 'formalization.yaml').read_text())
    schema = json.loads(Path(sys.argv[1]).read_text())
    jsonschema.Draft202012Validator(schema).validate(metadata)
    cfg = json.loads((ROOT / CONFIG).read_text())
    expected = ['STWProblemXXII.exists_uniformTracialCompletion_with_discontinuous_trace',
                'STWProblemXXII.exists_factorial_traciallyComplete_with_discontinuous_trace']
    assert cfg['theorem_names'] == expected
    assert cfg['challenge_module'] == ROOTS[0]
    assert cfg['solution_module'] == ROOTS[1]
    assert set(cfg['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    assert [x['declaration'] for x in metadata['status']['main_results']] == expected
    assert all(x['sorry_count'] == 0 and x['comparator_config'] == CONFIG
               and set(x['axioms']) == set(cfg['permitted_axioms'])
               for x in metadata['status']['main_results'])
    assert metadata['project']['license'] == 'Apache-2.0'
    assert metadata['sources'][0]['type'] == 'original-proof'
    assert 'Codex (OpenAI) wrote the submission prose' in metadata['automation']['notes']
    assert metadata['project']['authors'] == ['Sauers']
    assert metadata['project']['responsible_maintainers'] == ['SauersML']
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.0'
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': 'v4.32.0'}]
    assert json.loads((ROOT / 'lake-manifest.json').read_text())['packages'][0]['rev'] == \
        '81a5d257c8e410db227a6665ed08f64fea08e997'
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    tracked = [p for p in tracked if p]
    banned = re.compile(r'\.' + '(?:m' + 'd|mark' + 'down)\\b|READ' + 'ME', re.I)
    for path in tracked:
        p = ROOT / path
        assert not p.is_symlink(), path
        assert not banned.search(path), path
        assert not banned.search(p.read_text()), path
    assert sum((ROOT / p).stat().st_size for p in tracked) < 500 * 1024 ** 2
    lean_files = {p for p in tracked if p.endswith('.lean')}
    visited = set()
    queue = [m.replace('.', '/') + '.lean' for m in ROOTS]
    queue += [p for p in lean_files if p.startswith('scripts/')]
    holes = []
    while queue:
        path = queue.pop()
        if path in visited:
            continue
        assert path in lean_files, path
        visited.add(path)
        active = code((ROOT / path).read_text())
        assert not re.search(r'\b(?:admit|sorryAx|native_decide|implemented_by|extern)\b', active), path
        assert not re.search(r'^\s*(?:axiom|constant|unsafe|opaque)\b', active, re.M), path
        n = len(re.findall(r'\bsorry\b', active))
        if n:
            holes.append((path, n))
        for imp in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', active, re.M):
            for module in imp.split():
                if module.split('.')[0] in {'Mathlib', 'Lean'}:
                    continue
                queue.append(module.replace('.', '/') + '.lean')
    assert visited == lean_files, sorted(lean_files - visited)
    assert holes == [('Palomar/STWProblemXXIIChallenge.lean', 2)], holes
    challenge = (ROOT / 'Palomar/STWProblemXXIIChallenge.lean').read_text()
    solution = (ROOT / 'Palomar/STWProblemXXIISolution.lean').read_text()
    def shared(text):
        return text[text.index('-- BEGIN SHARED BLOCK'):text.index('-- END SHARED BLOCK')]
    assert shared(challenge) == shared(solution)
    print(f'PASS: schema, credits, package restrictions, import closure ({len(visited)} Lean files), '
          'shared definitions, and exactly two intentional Challenge holes.')


if __name__ == '__main__':
    main()
