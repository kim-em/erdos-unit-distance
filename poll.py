#!/usr/bin/env python3
"""Poll all tracked Aristotle projects; print one line per project: name, task status."""
import asyncio, sys
from pathlib import Path
import aristotlelib

TSV = Path("/home/kim/erdos-unit-distance/aristotle-projects.tsv")

async def one(line):
    pid, name = line.split("\t")[:2]
    try:
        p = await aristotlelib.Project.from_id(pid)
        tasks, _ = await p.get_tasks(limit=3)
        st = tasks[0].status.name if tasks else "NO_TASKS"
        pct = getattr(tasks[0], "percent_complete", "") if tasks else ""
    except Exception as e:
        st, pct = f"ERR {e}", ""
    return f"{name}\t{st}\t{pct}\t{pid}"

async def main():
    lines = [l for l in TSV.read_text().strip().split("\n") if l]
    res = await asyncio.gather(*(one(l) for l in lines))
    print("\n".join(res))

asyncio.run(main())
