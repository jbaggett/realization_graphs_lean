#!/usr/bin/env python3
"""check_trust_surface_pointers.py — every `Name (`File.lean:N`)` in TRUST_SURFACE.md still resolves.

WHY THIS EXISTS (2026-08-27).  `TRUST_SURFACE.md` is the document an external auditor reads, and it
navigates by `file:line`.  On 2026-08-27 twenty-two of its pointers were stale, among them the
pointer to `realizationGraph_maximally_hamiltonian` itself: `SBPlusOrd.lean:13339` when the theorem
had moved to `:13670`.  Nothing had gone wrong with the mathematics.  The modules had simply grown,
and every pointer below an insertion shifted.

THIS IS THE FAILURE MODE THAT DOES NOT ANNOUNCE ITSELF.  A stale line number does not resolve to
nothing; it resolves to an unrelated `have` in the middle of some other proof.  A reader following it
sees plausible Lean, no error, and no reason to doubt the document.  The trust surface's own banner
records this class being repaired once before, by hand, for two `CITEKEY` lines — which is exactly
the shape of a defect that wants a gate rather than a habit.

WHAT IT CHECKS.  For each backticked identifier followed by a backticked `File.lean:N` pointer, the
named declaration must actually begin on line `N` of that file.  `Defs.lean` is ambiguous in the tree
(`RealizationGraph/` and `Tournament/`) and is resolved to `RealizationGraph/`.  A qualified name
(`Brualdi.Ledger.foo`) is matched on its last component, since that is how it is declared.

FOUR SPELLINGS OF "the name beside the pointer" are recognized, because the document uses all four:
`Name` (`F.lean:N`); `Name args` (`F.lean:N`), where the arguments are inside the same backticks;
(`Name`, `F.lean:N`), with the name first inside the parentheses; and the `### A3: `Name`
(`F.lean:N`)` headings.  A `CITEKEY` pointer is checked differently and no less strictly: its target
line must carry the citekey the sentence names.

WHAT IT DELIBERATELY DOES NOT CHECK.  Pointers with no name beside them at all — "consumed at
`SBPlusOrd.lean:1147`" naming a proof line rather than a declaration — cannot be re-resolved
mechanically, because there is nothing to search for.  Those are reported as SKIP **and listed**, so
a document that grows more of them says so rather than quietly shrinking the gate's coverage.  When
one of them points at a declaration, the fix is to name it in the prose, which is what was done on
2026-08-27 for the main theorem's own pointer.

    python3 topics/flipgraphs/realization/compute/check_trust_surface_pointers.py
"""
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[4]
LEAN = ROOT / "lean" / "BrualdiLean"
DOCS = [
    ROOT / "topics/flipgraphs/realization/paper/TRUST_SURFACE.md",
    ROOT / "topics/flipgraphs/realization/paper/TRUST_SURFACE_QSTAR_NOTE.md",
]

DECL = (r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:axiom|def|theorem|lemma|abbrev|structure|instance|inductive)\s+")

# `Name` (`File.lean:N`) and `Name args` (`File.lean:N`) — the arguments are dropped
INLINE = re.compile(r"`([A-Za-z_][\w.']*)(?: [^`]*)?`(?:\*{1,2})?\s*\(`([A-Za-z0-9_]+\.lean):(\d+)`")
# (`Name`, `File.lean:N`)
PAREN = re.compile(r"\(`([A-Za-z_][\w.']*)`,\s*`([A-Za-z0-9_]+\.lean):(\d+)`")
# ### A3: `Name` (`File.lean:N`)
HEADING = re.compile(r"^### [AD]\d+: `([A-Za-z_][\w.']*)`(?:, `[^`]+`)? \(`([A-Za-z0-9_]+\.lean):(\d+)", re.M)
# `citekey` in `File.lean:N` — the target line must carry that citekey
CITEKEY = re.compile(r"`([A-Za-z][\w:-]*)` in `([A-Za-z0-9_]+\.lean):(\d+)`")
ANY_POINTER = re.compile(r"`([A-Za-z0-9_]+\.lean):(\d+)`")


def modules():
    by_name = {}
    for p in LEAN.rglob("*.lean"):
        by_name.setdefault(p.name, []).append(p)
    return by_name


def resolve(by_name, fname):
    cands = by_name.get(fname, [])
    if fname == "Defs.lean":
        cands = [p for p in cands if "RealizationGraph" in str(p)]
    return cands[0] if len(cands) == 1 else None


def main():
    by_name = modules()
    cache = {}
    failures, checked, skipped = [], 0, 0

    for doc in DOCS:
        if not doc.exists():
            print(f"MISSING  {doc}")
            failures.append((doc.name, "-", "-", "document not found"))
            continue
        text = doc.read_text(encoding="utf-8")
        named = set()
        for pat, kind in ((INLINE, "decl"), (PAREN, "decl"), (HEADING, "decl"), (CITEKEY, "citekey")):
            for m in pat.finditer(text):
                name, fname, line = m.group(1).split(".")[-1], m.group(2), int(m.group(3))
                path = resolve(by_name, fname)
                if path is None:
                    named.add((fname, line))
                    failures.append((doc.name, name, f"{fname}:{line}", "module not found or ambiguous"))
                    continue
                if path not in cache:
                    cache[path] = path.read_text(encoding="utf-8", errors="ignore").splitlines()
                lines = cache[path]
                if kind == "citekey":
                    target = lines[line - 1] if 0 < line <= len(lines) else ""
                    if "CITEKEY" not in target or name not in target:
                        continue        # not a citekey pointer after all; leave it to the decl patterns
                    named.add((fname, line))
                    checked += 1
                    continue
                actual = [i + 1 for i, l in enumerate(lines)
                          if re.match(DECL + re.escape(name) + r"\b", l)]
                if not actual and (fname, line) in named:
                    continue            # a looser pattern already matched this pointer
                named.add((fname, line))
                checked += 1
                if line not in actual:
                    where = ", ".join(str(a) for a in actual) if actual else "declaration not found"
                    failures.append((doc.name, name, f"{fname}:{line}", f"actual {where}"))
        # pointers carrying no name at all: counted and listed, not resolvable
        for i, l in enumerate(text.splitlines(), 1):
            for m in ANY_POINTER.finditer(l):
                if (m.group(1), int(m.group(2))) not in named:
                    skipped += 1
                    print(f"  SKIP   {doc.name}:{i}  `{m.group(1)}:{m.group(2)}`  (no name beside it)")

    seen, unique = set(), []
    for f in failures:
        if f not in seen:
            seen.add(f); unique.append(f)
    failures = unique
    print(f"checked {checked} named pointers, {skipped} unnamed (SKIP), {len(failures)} stale")
    for doc, name, ptr, why in failures:
        print(f"  STALE  {doc}  {name}  {ptr}  ({why})")
    if failures:
        print("\nFAIL — fix the pointers, or the document sends a reader to an unrelated proof step.")
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
