#!/usr/bin/env python3
"""check_axiom_provenance.py — join the Lean's cited axioms to the bibliography AND to §10.4.

WHY THIS EXISTS (2026-08-19).  `check_axiom_baseline.py` asserts that the cited-axiom set matches a
list maintained beside it.  Nothing compared that list to the PAPER's own claim about it, and the
paper's claim is a prose sentence with a number in it:

    §10.4  "complete relative to two inputs from outside this paper, together with Tyshkevich's
            canonical decomposition"

By 2026-08-19 the surface carried thirteen entries spanning at least seven distinct external sources.
Every entry had been added correctly, source-pinned and gated; what nothing checked was the SUM.
That is Class 10 of `PROSE_LEAN_GAPS.md`, and this is its gate.

THREE CHECKS

  1. Every cited axiom's docstring resolves to a citekey present in this paper's `references.bib`.
     "Nothing is cited unless its key is in that file" is the standing rule, and an axiom whose
     source is named only in prose cannot be audited mechanically.
  2. Every such citekey is actually cited SOMEWHERE in the manuscript.  A bibliography entry backing
     an axiom but appearing in no section is the shape `RG1979` took when the Ruch-Gutman sentence
     was removed on 2026-08-19.
  3. Every such citekey appears in §10.4, the section whose whole job is to list what the proof rests
     on.  This is the check that would have caught Class 10.

DELIBERATELY A REPORT, NOT A HARD GATE.  Docstrings legitimately name sources in prose ("Barrus
2016"), and an author-surname fallback is a heuristic and is NEVER counted as resolved.  It once matched
`AP1999` (Arikati-Peled) to axioms sourced to Hammer-Peled and Mahadev-Peled on the surname "Peled"
alone -- three different papers.  A surname is a hint for a human, never an attribution.  Exit status is 1 only when a
citekey that IS resolved is missing from §10.4 — the one condition that is mechanical and was the
actual failure.

    python3 topics/flipgraphs/realization/compute/check_axiom_provenance.py
"""
import io, re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[4]
LEAN = ROOT / "lean"
PAPER = ROOT / "topics" / "flipgraphs" / "realization" / "paper"
BIB = PAPER / "references.bib"
GATE = ROOT / "topics/flipgraphs/realization/compute/check_axiom_baseline.py"
ASSEMBLY = PAPER / "SEC_ASSEMBLY.md"


def cited_names():
    """The cited-axiom names, COMMENTS STRIPPED.

    This used to regex every double-quoted string in the block, comments included, so the phrase
    "count = 1 iff threshold" -- which sits inside a 2026-08-19 retirement note explaining that two
    modules each prove it -- was harvested as though it were an axiom.  It reported 8 cited entries
    where the manuscript says 7, and then dutifully reported the phantom as UNRESOLVED, which is how
    a scanner bug becomes a submission blocker in a handoff.  Names are qualified Lean identifiers;
    nothing else qualifies."""
    t = GATE.read_text(encoding="utf-8")
    block = t[t.index("EXPECT_CITED = {"):]
    block = block[:block.index("\n}")]
    code = "\n".join(re.sub(r"#.*$", "", line) for line in block.splitlines())
    return [n for n in re.findall(r'"([^"]+)"', code)
            if re.fullmatch(r"[A-Za-z_][\w.']*", n)]


def docstring_for(short):
    """The `/-- ... -/` immediately preceding `axiom <short>`, anywhere in the tree."""
    for f in LEAN.rglob("*.lean"):
        t = f.read_text(encoding="utf-8", errors="ignore")
        m = re.search(r"(/--(?:(?!-/).)*?-/)\s*axiom\s+" + re.escape(short) + r"\b", t, re.S)
        if m: return m.group(1), f.name
    return None, None


def main():
    keys = {}
    for m in re.finditer(r"^@\w+\{([^,]+),(.*?)\n\}", BIB.read_text(encoding="utf-8"), re.S | re.M):
        keys[m.group(1)] = m.group(2)
    prose = "\n".join(p.read_text(encoding="utf-8", errors="ignore")
                      for p in PAPER.glob("SEC_*.md"))
    a = ASSEMBLY.read_text(encoding="utf-8")
    i = a.find("## 10.4")
    sec104 = a[i:] if i >= 0 else ""
    in104 = set(re.findall(r"@([A-Za-z][\w:-]*)", sec104))

    resolved, unresolved, uncited, missing104 = {}, [], [], []
    for full in cited_names():
        short = full.split(".")[-1]
        if "native_decide" in full:
            unresolved.append((short[:44], "a finite computation, no source owed"))
            continue
        doc, where = docstring_for(short)
        if doc is None:
            unresolved.append((short, "NO DOCSTRING FOUND")); continue
        hit = [k for k in keys if re.search(r"\b" + re.escape(k) + r"\b", doc)]
        guess = []
        if not hit:                       # author-surname fallback, reported but NEVER trusted
            for k, body in keys.items():
                au = re.search(r"author\s*=\s*\{(.+?)\}", body, re.S)
                if not au: continue
                for surname in re.findall(r"([A-Z][a-z]{3,})\s*,", au.group(1)):
                    if re.search(r"\b" + surname + r"\b", doc): guess.append(k); break
        if not hit:
            why = (f"no citekey in docstring ({where})"
                   + (f"; surname only suggests {', '.join(sorted(set(guess)))}" if guess else ""))
            unresolved.append((short, why)); continue
        for k in hit:
            resolved.setdefault(k, []).append(short)
            if k not in prose: uncited.append((short, k))
            if k not in in104: missing104.append((short, k))

    print(f"cited entries: {len(cited_names())}   distinct sources resolved: {len(resolved)}\n")
    print("RESOLVED to a citekey in this paper's references.bib:")
    for k in sorted(resolved): print(f"  {k:36s} <- {', '.join(sorted(set(resolved[k])))}")
    if unresolved:
        print("\nUNRESOLVED (source named in prose only, or none) — triage by hand:")
        for s, why in unresolved: print(f"  {s:44s} {why}")
    if uncited:
        print("\n⚠ citekey backs an axiom but is CITED NOWHERE in the manuscript:")
        for s, k in sorted(set(uncited)): print(f"  {k:24s} (backs {s})")
    print(f"\n§10.4 names these citekeys: {', '.join(sorted(in104)) or '(none found)'}")
    if missing104:
        print("\n*** FAIL — resolved sources ABSENT from §10.4, the section that lists")
        print("    what the proof rests on:")
        for s, k in sorted(set(missing104)): print(f"      {k:24s} (backs {s})")
        return 1
    print("\nRESULT: every resolved source appears in §10.4.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
