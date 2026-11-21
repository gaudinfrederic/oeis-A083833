#!/usr/bin/env python3
"""scan_p0.py - P0 source-surface scanner (protocole v3).
Automate a etats : commentaires blocs imbriques /- ... -/, commentaires
de ligne --, chaines "..." (echappements \\ \"), litteraux char 'x'
(prime d'identifiant distingue : ' n'est un litteral que s'il ne suit
pas [A-Za-z0-9_']). Aucune regex sur le brut.
Usage : python scan_p0.py FICHIER [FICHIER ...]  -> exit 1 si rejet.
"""
import sys

FORBIDDEN_CODE = {
    "sorry", "admit", "axiom", "unsafe", "implemented_by", "extern",
    "csimp", "native_decide", "bv_decide", "initialize",
    "builtin_initialize", "run_meta",
}
FORBIDDEN_DEFS = {
    "notation", "macro", "macro_rules", "elab", "elab_rules", "syntax",
}
REVIEW_FLAGS = {"local", "scoped"}  # suivi de instance -> revue humaine

def strip(src):
    """Retourne le code avec commentaires/chaines blanchis (memes positions)."""
    out = list(src)
    i, n, depth = 0, len(src), 0
    state = "code"
    while i < n:
        c = src[i]
        if state == "code":
            if c == "-" and i + 1 < n and src[i + 1] == "-":
                out[i] = out[i + 1] = " "; i += 2; state = "line"
                continue
            if c == "/" and i + 1 < n and src[i + 1] == "-":
                out[i] = out[i + 1] = " "; i += 2; depth = 1; state = "block"
                continue
            if c == '"':
                out[i] = " "; i += 1; state = "str"; continue
            if c == "'":
                prev = src[i - 1] if i > 0 else " "
                if not (prev.isalnum() or prev in "_'"):
                    out[i] = " "; i += 1; state = "char"; continue
            i += 1; continue
        if state == "line":
            if c == "\n": state = "code"
            else: out[i] = " "
            i += 1; continue
        if state == "block":
            if c == "/" and i + 1 < n and src[i + 1] == "-":
                out[i] = out[i + 1] = " "; depth += 1; i += 2; continue
            if c == "-" and i + 1 < n and src[i + 1] == "/":
                out[i] = out[i + 1] = " "; depth -= 1; i += 2
                if depth == 0: state = "code"
                continue
            if c != "\n": out[i] = " "
            i += 1; continue
        if state == "str":
            if c == "\\" and i + 1 < n:
                out[i] = out[i + 1] = " "; i += 2; continue
            out[i] = " " if c != "\n" else "\n"
            if c == '"': state = "code"
            i += 1; continue
        if state == "char":
            if c == "\\" and i + 1 < n:
                out[i] = out[i + 1] = " "; i += 2; continue
            out[i] = " "
            if c == "'": state = "code"
            i += 1; continue
    return "".join(out)

def words_at(code):
    """(mot, ligne) pour chaque identifiant du code blanchi."""
    for ln, line in enumerate(code.split("\n"), 1):
        w = ""
        for ch in line + " ":
            if ch.isalnum() or ch in "_'":
                w += ch
            else:
                if w: yield w, ln
                w = ""

def scan(path):
    code = strip(open(path, encoding="utf-8").read())
    bad, review = [], []
    ws = list(words_at(code))
    for i, (w, ln) in enumerate(ws):
        if w in FORBIDDEN_CODE or w in FORBIDDEN_DEFS or w == "IO." or w.startswith("IO"):
            if w in FORBIDDEN_CODE or w in FORBIDDEN_DEFS:
                bad.append(f"{path}:{ln}: interdit `{w}`")
        if w in REVIEW_FLAGS and i + 1 < len(ws) and ws[i + 1][0] == "instance":
            review.append(f"{path}:{ln}: revue `{w} instance`")
    return bad, review

def main():
    bad_all, rev_all = [], []
    for p in sys.argv[1:]:
        b, r = scan(p)
        bad_all += b; rev_all += r
    for m in bad_all + rev_all: print(m)
    if bad_all:
        print(f"REJET: {len(bad_all)} construction(s) interdite(s)")
        sys.exit(1)
    print(f"P0 OK ({len(rev_all)} point(s) de revue)")

if __name__ == "__main__":
    main()
