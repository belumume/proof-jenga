"""Inline the dependency data and the Lean proofs into the page.

    lake env lean scripts/Deps.lean > docs/data.json
    python3 scripts/build_site.py

reads docs/page.html and writes docs/index.html, one self-contained page.
With --fragment PATH it also writes the page body without the document wrapper.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SITE = ROOT / "docs"

# Lean theorem name -> source file
FILES = {
    "Jenga.euclid": "Euclid.lean",
    "Jenga.fermat": "Fermat.lean",
    "Jenga.bertrand": "Bertrand.lean",
    "Jenga.erdos": "Erdos.lean",
    "Jenga.erdosRebuilt": "ErdosRebuilt.lean",
    "Jenga.dirichlet": "Dirichlet.lean",
}


def theorem_text(path: pathlib.Path, name: str) -> str:
    """The `theorem <name>` block from a Lean file, without the module docstring."""
    src = path.read_text()
    short = name.split(".")[-1]
    start = src.index(f"theorem {short} ")
    end = src.find("\nend ", start)
    return src[start:end].rstrip() + "\n"


def main() -> None:
    data = json.loads((SITE / "data.json").read_text())
    proofs_dir = ROOT / "Jenga" / "Proofs"
    data["sources"] = {
        name: {"file": f"Jenga/Proofs/{file}", "code": theorem_text(proofs_dir / file, name)}
        for name, file in FILES.items()
    }
    missing = {p["proof"] for p in data["proofs"]} - set(FILES)
    if missing:
        raise SystemExit(f"no source file mapped for {sorted(missing)}")
    page = (SITE / "page.html").read_text()
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    out, n = re.subn(r"/\*DATA\*/null", lambda _: payload, page)
    if n != 1:
        raise SystemExit("expected exactly one /*DATA*/null marker in page.html")
    doc = (
        '<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
        "</head>\n<body>\n" + out + "\n</body>\n</html>\n"
    )
    (SITE / "index.html").write_text(doc)
    print(f"wrote {SITE / 'index.html'} ({len(doc):,} bytes)")
    if len(sys.argv) == 3 and sys.argv[1] == "--fragment":
        pathlib.Path(sys.argv[2]).write_text(out)
        print(f"wrote {sys.argv[2]}")


if __name__ == "__main__":
    main()
