"""Download the two FRED series used by coupled_stochastic/real_env.py and check they are
byte-identical to the files the pre-registered run used. Usage: python fetch_fred.py [dest_dir]"""
import sys, os, hashlib, urllib.request
SERIES = {  # id: (end date, sha256 of the file used in the frozen run)
    "VIXCLS": ("2026-07-01", "b891dcbb963850281932fe7b2ee276e4b24a759bbbd00a000cbc73ff0276719f"),
    "DTWEXBGS": ("2026-06-26", "2437d34b117c81dee64aa0a0ad3c29c1dc0a6318abdd286e9179144bb970a4e6"),
}
dest = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
os.makedirs(dest, exist_ok=True); ok = True
for s, (end, want) in SERIES.items():
    url = f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={s}&cosd=2018-01-01&coed={end}"
    req = urllib.request.Request(url, headers={"User-Agent": "python-urllib"})
    b = urllib.request.urlopen(req, timeout=60).read()
    p = os.path.join(dest, f"fred_{s}.csv"); open(p, "wb").write(b)
    got = hashlib.sha256(b).hexdigest(); match = got == want; ok &= match
    print(f"{s}: {'identical to the frozen run' if match else 'DIFFERS (FRED revision?) ' + got}")
sys.exit(0 if ok else 1)
