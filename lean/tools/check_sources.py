"""Check the source files and exact declarations against the proof index (modules.json, theorems.json)."""

from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
modules = json.loads((ROOT / "modules.json").read_text())["modules"]
theorems = json.loads((ROOT / "theorems.json").read_text())["theorems"]


def without_comments(source):
    """Remove nested Lean comments while retaining line boundaries and strings."""
    output = list(source)
    i = 0
    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            end, depth = i + 2, 1
            while end < len(source) and depth:
                if source.startswith("/-", end):
                    depth += 1
                    end += 2
                elif source.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        else:
            i += 1
            continue
        output[i:end] = ["\n" if c == "\n" else " " for c in source[i:end]]
        i = end
    return "".join(output)


sources = {}
changed_files = []
for module in modules:
    path = ROOT.parent / module["file"]
    source = path.read_text()
    sources[module["file"]] = source
    if hashlib.sha256(source.encode()).hexdigest() != module["sha256"]:
        changed_files.append(module["file"])

changed_statements = []
for theorem in theorems:
    source = sources[theorem["file"]]
    remainder = "\n".join(source.splitlines()[theorem["line"] - 1:])
    declaration = theorem.get("alias_source", theorem["statement"])
    if not remainder.startswith(declaration):
        changed_statements.append(theorem["name"])

mathematical = [m for m in modules if m["module"].startswith("Comparison")]
clean = "\n".join(without_comments(sources[m["file"]]) for m in mathematical)
explicit = len(re.findall(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma)\s+",
    clean, re.M))
aliases = len(re.findall(r"^alias\s+", clean, re.M))
forbidden = re.findall(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\s+", clean, re.M)
print(f"Comparison source modules: {len(mathematical)}")
print(f"Theorem/lemma statements: {explicit}")
print(f"Theorem aliases: {aliases}")
print(f"Source theorem declarations: {explicit + aliases}")
print(f"Changed source files: {len(changed_files)}")
print(f"Changed indexed declarations: {len(changed_statements)}")
print(f"Forbidden proof declarations/tactics: {len(forbidden)}")
if changed_files or changed_statements or forbidden or explicit + aliases != len(theorems):
    for item in changed_files + changed_statements + forbidden:
        print(item)
    raise SystemExit("Source and theorem index: FAIL")
print("Source and theorem index: PASS")
