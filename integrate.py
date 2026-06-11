#!/usr/bin/env python3
"""Splice Aristotle per-sorry solutions back into Framework.lean.

For each (solution file, target, helpers): replace the target theorem's
`:= by sorry` body with the solution's proof (keeping the framework's doc
comment), and insert any helper declarations immediately before it.
"""
import re, sys
from pathlib import Path

FRAMEWORK = Path("/home/kim/worktrees/mathlib4/erdos-unit-distance/ErdosUnitDistance/Framework.lean")

DECL_RE = re.compile(
    r"^(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|example|axiom)\s+([A-Za-z0-9_']+)")
CHUNK_START = re.compile(
    r"^(/--|/-!|/-\s|private|theorem|lemma|def|noncomputable|instance|example|axiom|omit|open|"
    r"section|end|variable|namespace|import)")
OPEN_IN = re.compile(r"^open .*\bin\s*$")


def parse_chunks(text):
    lines = text.split("\n")
    raw, cur, in_comment = [], [], False
    for ln in lines:
        if not in_comment and CHUNK_START.match(ln) and cur:
            raw.append(cur)
            cur = [ln]
        else:
            cur.append(ln)
        if in_comment:
            if "-/" in ln:
                in_comment = False
        elif ln.lstrip().startswith(("/--", "/-!", "/- ")) and "-/" not in ln:
            in_comment = True
    if cur:
        raw.append(cur)
    out, pend_doc, pend_open = [], None, None
    for ch in raw:
        body = "\n".join(ch)
        first = ch[0]
        if first.startswith(("/--", "/-!", "/- ")) and not DECL_RE.search(body):
            if pend_doc:
                out.append((None, pend_doc))
            pend_doc = body
            continue
        if OPEN_IN.match(first.strip()) and not re.search(r"^\s*(private\s+)?(theorem|lemma|def|instance)", body, re.M):
            pend_open = body.rstrip()
            continue
        name = None
        for ln in ch:
            m = DECL_RE.match(ln)
            if m:
                name = m.group(1)
                break
        full = body
        if pend_doc:
            full = pend_doc + "\n" + full
        if pend_open:
            full = pend_open + "\n" + full
        pend_doc, pend_open = None, None
        out.append((name, full))
    if pend_doc:
        out.append((None, pend_doc))
    return out


def decl_onward(chunk_text, name):
    """Strip a leading doc comment, keeping set_option/open-in prefix lines."""
    lines = chunk_text.split("\n")
    start = 0
    if lines[0].lstrip().startswith(("/--", "/-!", "/- ")):
        for i, ln in enumerate(lines):
            if "-/" in ln:
                start = i + 1
                break
    return "\n".join(lines[start:])


def doc_prefix(chunk_text, name):
    lines = chunk_text.split("\n")
    for i, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if m and m.group(1) == name:
            return "\n".join(lines[:i])
    raise ValueError(f"decl {name} not found in chunk")


def integrate(solution_path, target, helpers):
    sol = {n: t for n, t in parse_chunks(Path(solution_path).read_text()) if n}
    fw_text = FRAMEWORK.read_text()
    fw = parse_chunks(fw_text)
    new_chunks = []
    done = False
    for name, text in fw:
        if name == target:
            for h in helpers:
                new_chunks.append((h, sol[h]))
            merged = doc_prefix(text, target)
            if merged:
                merged += "\n"
            merged += decl_onward(sol[target], target)
            new_chunks.append((name, merged))
            done = True
        else:
            new_chunks.append((name, text))
    assert done, f"target {target} not found in framework"
    FRAMEWORK.write_text("\n".join(t for _, t in new_chunks))
    print(f"integrated {target} (+{len(helpers)} helpers)")


JOBS = {
    "q3inf": ("infinite_setOf_q3", []),
    "gridpigeon": ("finite_and_card_le_of_separated",
                   ["cell_index_mem", "cell_index_diff",
                    "norm_lt_of_re_im_bound", "cellCount_le"]),
    "euclidcopy": ("exists_euclidean_copy", []),
    "classnum": ("classNumber_le_bound", []),
    "geomcore": ("geometric_core", []),
    "kfitc": ("Kf_isTotallyComplex", []),
    "kffd": ("Kf_finiteDimensional", []),
    "latticebox": ("lattice_inter_box_finite_card", []),
    "translates": ("le_unitPairsC_of_translates", []),
    "doubling": ("ncard_box_two_le_doubling", []),
    "twomul": ("two_mul_unitDist", []),
    "final": ("erdos_unit_distance_uniform_constant_false", ["exists_params"]),
    "goodpointset": ("exists_good_pointset",
                     ["finrank_adjoin_finset_le", "Kf_finrank_le", "Kf_card_le",
                      "mink_apply", "norm_mink_apply", "mink_injective",
                      "absNorm_le_prod_places", "mink_sep_aux",
                      "rpow_balance_lt", "rpow_balance_le", "box_count_bound"]),
}

if __name__ == "__main__":
    import glob
    for key in sys.argv[1:]:
        target, helpers = JOBS[key]
        solfile = glob.glob(f"/tmp/sol-{key}/*/Submission.lean")[0]
        integrate(solfile, target, helpers)
