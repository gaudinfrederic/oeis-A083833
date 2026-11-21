import hashlib, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
out = []
for f in sorted(os.listdir(".")):
    if os.path.isfile(f) and f != "MANIFEST.sha256":
        out.append(f"{hashlib.sha256(open(f, 'rb').read()).hexdigest()}  {f}")
open("MANIFEST.sha256", "w", encoding="utf-8", newline="").write("\n".join(out) + "\n")
print(len(out), "files hashed")
