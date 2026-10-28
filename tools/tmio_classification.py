#!/usr/bin/env python3
"""Check/query source-authored connection theorems' @[tmio ...] attributes.

No classification table is maintained. Lean's registered attribute is the source
of ownership; this standard-library preflight reads its explicit source notation
without building dependencies. The Lean environment audit independently checks
elaborated declarations, including connection types expressed through aliases.
"""

from __future__ import annotations

import argparse
import bisect
import json
import re
import sys
from collections import Counter
from pathlib import Path

KINDS = ('T', 'M', 'TM', 'MI', 'IO')
MODIFIERS = r'(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
DECLARATION = re.compile(r'^[ \t]*(?P<mods>' + MODIFIERS +
                         r')(?P<kind>theorem|lemma)\s+(?P<name>[^\s({:]+)', re.M)


class ClassificationError(ValueError):
    pass


def code_only(source: str) -> str:
    """Mask nested comments/strings while keeping source offsets and newlines."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        c = source[i]
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if c == '\n' else ' '); i += 1
        elif quoted:
            if c == '\\' and i + 1 < len(source):
                out.extend('  '); i += 2
            elif c == '"':
                quoted = False; out.append(' '); i += 1
            else:
                out.append('\n' if c == '\n' else ' '); i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif c == '"':
            quoted = True; out.append(' '); i += 1
        else:
            out.append(c); i += 1
    return ''.join(out)


def attributes(code: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Mask whole attribute blocks, including multiline/nested tactic options."""
    masked, spans, pos = list(code), [], 0
    while (start := code.find('@[', pos)) >= 0:
        depth, end = 1, start + 2
        while end < len(code) and depth:
            if code[end] == '[':
                depth += 1
            elif code[end] == ']':
                depth -= 1
            end += 1
        if depth:
            raise ClassificationError('Unterminated attribute block')
        spans.append((start, end, code[start+2:end-1]))
        for index in range(start, end):
            if masked[index] != '\n':
                masked[index] = ' '
        pos = end
    return ''.join(masked), spans


def attribute_kinds(body: str) -> list[str]:
    items, depth, start = [], 0, 0
    for index, char in enumerate(body):
        if char in '([{':
            depth += 1
        elif char in ')]}':
            depth -= 1
        elif char == ',' and depth == 0:
            items.append(body[start:index].strip()); start = index + 1
    items.append(body[start:].strip())
    return [item[4:].strip() for item in items if re.match(r'tmio\b', item)]


def scan_connections(root: Path) -> dict[str, dict]:
    found = {}
    for path in sorted((root / 'theorem').rglob('*.lean')):
        code = code_only(path.read_text(encoding='utf-8'))
        declaration_code, spans = attributes(code)
        starts, namespaces, stack, pos = [], [], [], 0
        for line in declaration_code.splitlines(keepends=True):
            starts.append(pos)
            namespaces.append('.'.join(n for k, n in stack if k == 'namespace'))
            ns = re.match(r'^\s*namespace\s+(\S+)', line)
            section = re.match(r'^\s*(?:noncomputable\s+)?section\b\s*(\S+)?', line)
            end = re.match(r'^\s*end(?:\s|$)', line)
            if ns:
                stack.append(('namespace', ns[1]))
            elif section:
                stack.append(('section', section[1] or ''))
            elif end and stack:
                stack.pop()
            pos += len(line)
        declarations = list(DECLARATION.finditer(declaration_code))
        for index, match in enumerate(declarations):
            if 'private' in match['mods'].split():
                continue
            limit = declarations[index+1].start() if index+1 < len(declarations) else len(code)
            depth, stop = 0, None
            for i in range(match.end(), limit):
                if depth == 0 and code.startswith(':=', i):
                    stop = i; break
                if code[i] in '([{⦃':
                    depth += 1
                elif code[i] in ')]}⦄':
                    depth -= 1
            header = code[match.end():stop if stop is not None else limit]
            if not re.search(r'\bconnection%\s*\(', header):
                continue
            if stop is None:
                raise ClassificationError(f'Cannot parse connection declaration: {path}:{match["name"]}')
            namespace = namespaces[bisect.bisect_right(starts, match.start())-1]
            name = match['name']
            if name.startswith('_root_.'):
                name = name.removeprefix('_root_.')
            elif namespace:
                name = namespace + '.' + name
            if name in found:
                raise ClassificationError(f'Duplicate source connection: {name}')
            kinds, before = [], match.start('kind')
            for start, end, body in reversed(spans):
                if end > before:
                    continue
                between = code[end:before]
                if not re.fullmatch(r'\s*' + MODIFIERS, between):
                    break
                kinds[:0] = attribute_kinds(body)
                before = start
            relative = path.relative_to(root).as_posix()
            found[name] = {'name':name,'module':relative[:-5].replace('/', '.'),
                           'path':relative,'line':code.count('\n',0,match.start('kind'))+1,
                           'kinds':kinds}
    return found


def validate(root: Path) -> dict[str, int]:
    entries = scan_connections(root)
    if not entries:
        raise ClassificationError('No source connection theorems found')
    errors = []
    for entry in entries.values():
        kinds = entry['kinds']
        if len(kinds) != 1:
            errors.append(f'{entry["path"]}:{entry["line"]} {entry["name"]}: '
                          f'expected exactly one @[tmio ...], found {kinds}')
        elif kinds[0] not in KINDS:
            errors.append(f'{entry["name"]}: invalid tmio kind {kinds[0]}; expected {KINDS}')
    if errors:
        raise ClassificationError('\n'.join(errors))
    counts = Counter(e['kinds'][0] for e in entries.values())
    return {kind:counts[kind] for kind in KINDS}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', nargs='?', choices=['check','list','show'], default='check')
    parser.add_argument('query', nargs='?')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        counts = validate(root)
        if args.command == 'check':
            print(f'POWERLIB_TMIO_SOURCE_OK: {sum(counts.values())} connection theorems; ' +
                  ', '.join(f'{kind} {counts[kind]}' for kind in KINDS))
        elif args.command == 'list':
            if args.query not in KINDS:
                raise ClassificationError('list requires T, M, TM, MI or IO')
            for entry in scan_connections(root).values():
                if entry['kinds'] == [args.query]:
                    print(f'{args.query}\t{entry["path"]}:{entry["line"]}\t{entry["name"]}')
        else:
            entries = scan_connections(root)
            if args.query not in entries:
                raise ClassificationError(f'No source connection named {args.query}')
            print(json.dumps(entries[args.query],ensure_ascii=False,indent=2))
        return 0
    except (ClassificationError, OSError) as error:
        print(f'TMIO classification error: {error}',file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
