# Tools

| Script | Purpose |
|---|---|
| `build_all.sh` | strict build of all project sessions, keeping heaps |
| `check_all.sh` | build, then oracle/redundancy checks (`check/`), paper listings, counts |
| `check/` | check sessions; `project_checks.ML` audits oracles and finds duplicate facts, duplicate definitions and name clashes; reports in `check/output/` |
| `watch_build.sh SESSION [LIMIT]` | verbose build that stops a command running longer than LIMIT s and names it |
| `eval.sh FILE [LINE] [LOGIC]` | per-command check and timing of a scratch theory (`isabelle eval_at`) |
| `chk.sh [SESSION]` | build a scratch session in `wip/` |
| `paper_listings.py` | the paper's Isabelle listings against the sources |
| `paper_links.py [REV]` | repoint the paper's source links to a commit (commit the theories first) |
| `counts.py` | lines and results per level, as in the paper |

Settings (Isabelle binary, AFP path, session list) are in `env.sh`.
