#!/usr/bin/env python3
"""Checks on the proof sources and on Rocq's assumption report.

Used by tools/check.sh:

  check-proofs.py sources FILE.v ...
      Fails if a source file uses a command that assumes something without
      proof or switches off one of the kernel's checks. Comments and strings
      are ignored. Variable, Hypothesis and Context are accepted inside a
      Section only; outside one they declare axioms.

  check-proofs.py report PROOF_LOG ALLOWED_AXIOMS EXPECTED_CLOSED
      Reads what `Print Assumptions` printed for the theorems that Checker.v
      names. Every line of every tagged block has to be understood: an axiom
      on the allow-list, or "Closed under the global context". Anything else
      fails, including Rocq's notes that a definition "is assumed to be
      guarded" or relies on an unsafe feature. The <spec> block must hold
      exactly EXPECTED_CLOSED closed theorems and nothing else.

The second check is the one that matters: it is Rocq's own account of what
each theorem depends on. The first catches the same things earlier and names
the line.
"""
import re
import sys

FORBIDDEN = [
    (r"\bAdmitted\b", "an admitted proof"),
    (r"\badmit\b", "the admit tactic"),
    (r"\bgive_up\b", "the give_up tactic"),
    (r"\bAdmit\s+Obligations\b", "admitted obligations"),
    (r"\bAxioms?\b", "an axiom"),
    (r"\bParameters?\b", "a parameter"),
    (r"\bConjectures?\b", "a conjecture"),
    (r"\bUnset\s+(Guard|Positivity|Universe)\s+Checking\b", "a kernel check switched off"),
    (r"\bbypass_check\b", "a kernel check bypassed"),
]
SECTION_ONLY = re.compile(r"^(?:(?:Local|Global)\s+)?(Variables?|Hypothes[ie]s|Context)\b")
OPENER = re.compile(
    r"^(?:(?:Local|Global)\s+)?(Section|Module(?:\s+Type)?|End)\s+([A-Za-z_][A-Za-z0-9_']*)")


def strip_comments_and_strings(text):
    """Replace comments (which nest) and string literals by spaces, keeping
    newlines so that line numbers stay right."""
    out, i, depth, in_string = [], 0, 0, False
    while i < len(text):
        two = text[i:i + 2]
        ch = text[i]
        if in_string:
            if ch == '"':
                in_string = False
            out.append("\n" if ch == "\n" else " ")
            i += 1
        elif two == "(*":
            depth += 1
            out.append("  ")
            i += 2
        elif two == "*)" and depth:
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if ch == "\n" else " ")
            i += 1
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def check_sources(paths):
    problems = []
    for path in paths:
        code = strip_comments_and_strings(open(path, encoding="utf-8").read())
        for pattern, what in FORBIDDEN:
            for m in re.finditer(pattern, code):
                line = code.count("\n", 0, m.start()) + 1
                problems.append(f"{path}:{line}: {what} ({m.group(0)})")
        # Sentences end with a full stop followed by white space.
        stack, start = [], 0
        for m in re.finditer(r"\.(\s|$)", code):
            sentence = code[start:m.start()].strip()
            line = code.count("\n", 0, start + len(code[start:m.start()]) - len(code[start:m.start()].lstrip())) + 1
            start = m.end()
            opener = OPENER.match(sentence)
            if opener:
                kind, name = opener.group(1), opener.group(2)
                if kind == "End":
                    if stack and stack[-1][1] == name:
                        stack.pop()
                elif ":=" not in sentence:
                    stack.append(("S" if kind == "Section" else "M", name))
                continue
            if SECTION_ONLY.match(sentence) and not any(k == "S" for k, _ in stack):
                problems.append(f"{path}:{line}: {sentence.split()[0]} outside a Section declares an axiom")
    for p in problems:
        print("  " + p)
    return not problems


def check_report(log_path, allowed_path, expected_closed):
    allowed = {l.strip() for l in open(allowed_path, encoding="utf-8")
               if l.strip() and not l.startswith("#")}
    blocks, current, seen_axioms_header = {}, None, False
    problems = []
    for raw in open(log_path, encoding="utf-8", errors="replace"):
        line = raw.rstrip("\n")
        tag = re.fullmatch(r"<(/?)([a-z_]+)>", line.strip())
        if tag:
            closing, name = tag.group(1) == "/", tag.group(2)
            if not closing:
                if name in blocks:
                    problems.append(f"block <{name}> appears twice")
                blocks[name] = {"axioms": [], "closed": 0}
                current, seen_axioms_header = name, False
            else:
                if current != name:
                    problems.append(f"</{name}> without <{name}>")
                current = None
            continue
        if current is None or not line.strip():
            continue
        block = blocks[current]
        if line.strip() == "Closed under the global context":
            block["closed"] += 1
            seen_axioms_header = False
        elif line.strip() == "Axioms:":
            seen_axioms_header = True
        elif seen_axioms_header and line[0].isspace() and block["axioms"]:
            pass  # the type of the previous axiom, continued
        elif seen_axioms_header and re.match(r"^\S+ :( |$)", line):
            block["axioms"].append(line.split(" :", 1)[0])
        else:
            problems.append(f"<{current}>: line not understood: {line.strip()[:90]}")

    for name in ("halts_allowed", "eff_close_time_code", "trap_is_fatal", "spec"):
        if name not in blocks:
            problems.append(f"no report for <{name}>")
    for name, block in blocks.items():
        for axiom in block["axioms"]:
            if axiom not in allowed:
                problems.append(f"<{name}>: {axiom} is not on the allow-list")
        if name != "spec" and not block["axioms"] and block["closed"] != 1:
            problems.append(f"<{name}>: no assumption report")
    spec = blocks.get("spec")
    if spec and (spec["axioms"] or spec["closed"] != expected_closed):
        problems.append(f"<spec>: expected {expected_closed} closed theorems and no axioms, "
                        f"found {spec['closed']} closed and {len(spec['axioms'])} axioms")

    for p in problems:
        print("  " + p)
    if not problems:
        used = sorted({a for b in blocks.values() for a in b["axioms"]})
        print(f"   {len(used)} primitives, all on the allow-list; "
              f"{spec['closed']} specification theorems depend on nothing")
    return not problems


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "sources":
        ok = check_sources(sys.argv[2:])
    elif len(sys.argv) == 5 and sys.argv[1] == "report":
        ok = check_report(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    else:
        sys.exit(__doc__)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
