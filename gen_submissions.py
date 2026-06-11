#!/usr/bin/env python3
"""Generate per-sorry Aristotle submission projects from Framework.lean.

For each target, emit a project dir containing Submission.lean = the prefix
of Framework.lean up to and including the target declaration, with sorried
theorems outside the dependency set removed (their doc comments too).
Structural sorries (those referenced by always-kept proved decls/instances)
are always retained.  Aristotle rejects `axiom`s in the solve file, but per
Zulip guidance handles multiple small sorried theorems individually, so
dependencies stay as sorried theorems and the prompt names the one target.
"""
import re, sys, shutil
from pathlib import Path

FRAMEWORK = Path("/home/kim/worktrees/mathlib4/erdos-unit-distance/ErdosUnitDistance/Framework.lean")
OUTROOT = Path("/tmp/aristotle-jobs")
TOOLCHAIN = "leanprover/lean4:v4.28.0\n"

STRUCTURAL = {"infinite_setOf_q3", "infinite_setOf_p1", "Kf_finiteDimensional",
              "Kf_isTotallyComplex", "Kf_isAbelianGalois"}

GEOM = {"two_mul_unitDist", "exists_euclidean_copy",
        "finite_and_card_le_of_separated", "lattice_inter_box_finite_card",
        "ncard_box_two_le_doubling", "le_unitPairsC_of_translates"}

# target -> (extra sorried deps to keep, minimal?)
TARGETS = {
    "two_mul_unitDist": (set(), False),
    "exists_euclidean_copy": ({"two_mul_unitDist"}, False),
    "finite_and_card_le_of_separated": (set(), False),
    "lattice_inter_box_finite_card": ({"finite_and_card_le_of_separated"}, False),
    "ncard_box_two_le_doubling": (set(), False),
    "le_unitPairsC_of_translates": (set(), False),
    "geometric_core": (GEOM, False),
    "infinite_setOf_q3": (set(), False),
    "infinite_setOf_p1": (set(), False),
    "m_ge": (set(), False),
    "q3_poly_bound": (set(), False),
    "p1_poly_bound": (set(), False),
    "log_m_le": ({"p1_poly_bound"}, False),
    "Kf_finiteDimensional": (set(), False),
    "Kf_finrank": (set(), False),
    "Kf_isTotallyComplex": (set(), False),
    "Kf_isAbelianGalois": (set(), False),
    "card_ideal_absNorm_le": (set(), False),
    "classNumber_le_bound": ({"card_ideal_absNorm_le"}, False),
    "units_sq_index_le": (set(), False),
    "Kf_discr_le": (set(), False),
    "log_classNumber_Kf_le": ({"classNumber_le_bound", "Kf_discr_le", "q3_poly_bound"}, False),
    "exists_ideal_family": (set(), False),
    "arithmetic_construction": ({"exists_ideal_family", "units_sq_index_le"}, False),
    "exists_good_pointset": (GEOM | {"geometric_core", "arithmetic_construction",
                                      "units_sq_index_le", "exists_ideal_family"}, False),
    "key_inequality": (set(), True),
    "erdos_unit_distance_uniform_constant_false": ("ALL", False),
}

DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:theorem|def|abbrev|instance|example|axiom)\s*([A-Za-z0-9_']*)")
CHUNK_START = re.compile(
    r"^(/--|/-!|theorem|def|noncomputable|instance|example|axiom|omit|open|"
    r"section|end|variable|namespace|import)")
OPEN_IN = re.compile(r"^open .*\bin\s*$")


def parse_chunks(text):
    lines = text.split("\n")
    chunks, cur, in_comment = [], [], False
    for ln in lines:
        if not in_comment and CHUNK_START.match(ln) and cur:
            chunks.append(cur)
            cur = [ln]
        else:
            cur.append(ln)
        # track doc/block comment state (no nesting in this file)
        if in_comment:
            if "-/" in ln:
                in_comment = False
        elif (ln.lstrip().startswith(("/--", "/-!", "/-")) and "-/" not in ln):
            in_comment = True
    if cur:
        chunks.append(cur)
    out = []  # (name|None, is_sorry, text)
    pending_doc, pending_open = None, None
    for ch in chunks:
        body = "\n".join(ch)
        first = ch[0]
        if first.startswith("/--"):
            pending_doc = body
            continue
        if OPEN_IN.match(first.strip()) and not re.search(r"^\s*(theorem|def|instance)", body, re.M):
            pending_open = body.rstrip()
            continue
        name = None
        for ln in ch:
            m = DECL_RE.match(ln)
            if m and m.group(1):
                name = m.group(1)
                break
        is_sorry = bool(re.search(r"^\s*sorry\s*$", body, re.M))
        full = body
        if pending_doc:
            full = pending_doc + "\n" + full
        if pending_open:
            full = pending_open + "\n" + full
        pending_doc, pending_open = None, None
        out.append((name, is_sorry, full))
    return out


def gen(target, deps, minimal, chunks):
    keep_sorries = STRUCTURAL | (set() if deps == "ALL" else set(deps)) | {target}
    out, found = [], False
    for name, is_sorry, body in chunks:
        if minimal and name != target:
            # keep only imports/namespace/open/section scaffolding + target
            if not re.match(r"^(import|namespace|open|section|end|variable|/-!)", body.lstrip()):
                continue
            if name is not None:
                continue
        if is_sorry and name != target and deps != "ALL" and name not in keep_sorries:
            continue
        out.append(body)
        if name == target:
            found = True
            break
    assert found, f"target {target} not found"
    # close any open sections/namespace
    txt = "\n".join(out)
    opens = re.findall(r"^section (\w+)", txt, re.M)
    closes = re.findall(r"^end (\w+)", txt, re.M)
    for s in reversed(opens):
        if closes.count(s) < opens.count(s):
            txt += f"\n\nend {s}"
            closes.append(s)
    if "namespace Erdos" in txt and "end Erdos" not in txt:
        txt += "\n\nend Erdos"
    return txt + "\n"


def main():
    text = FRAMEWORK.read_text()
    chunks = parse_chunks(text)
    names = [n for n, s, _ in chunks if s]
    print("sorried decls found:", names, file=sys.stderr)
    only = sys.argv[1:] or list(TARGETS)
    for tgt in only:
        deps, minimal = TARGETS[tgt]
        proj = OUTROOT / tgt
        if proj.exists():
            shutil.rmtree(proj)
        proj.mkdir(parents=True)
        (proj / "Submission.lean").write_text(gen(tgt, deps, minimal, chunks))
        (proj / "lean-toolchain").write_text(TOOLCHAIN)
        print(f"wrote {proj}/Submission.lean")


if __name__ == "__main__":
    main()
