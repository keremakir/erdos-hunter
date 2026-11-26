import json
import re
import subprocess
from pathlib import Path

ROOT = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter")
ENV = dict(
    line.strip().split("=", 1)
    for line in (ROOT / ".env").read_text(encoding="utf-8").splitlines()
    if "=" in line and not line.startswith("#")
)
KEY = ENV["OPENROUTER_API_KEY"]


def curl_json(url, method="GET", payload=None, timeout=25):
    cmd = [
        "curl.exe", "-4", "-sS", "--max-time", str(timeout),
        "-X", method,
        "-H", f"Authorization: Bearer {KEY}",
        "-H", "Content-Type: application/json",
        "-H", "HTTP-Referer: https://localhost",
        "-H", "X-Title: Erdos-Hunter",
        url,
    ]
    if payload is not None:
        cmd.extend(["-d", json.dumps(payload)])
    res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    return json.loads(res.stdout)


print("=== 1. TESTING PAID VS FREE MODEL ACCESS ON OPENROUTER ===")
test_paid = curl_json(
    "https://openrouter.ai/api/v1/chat/completions",
    method="POST",
    payload={"model": "deepseek/deepseek-v3.2", "messages": [{"role": "user", "content": "Reply OK"}], "max_tokens": 5},
)
print("Paid test (deepseek/deepseek-v3.2):", json.dumps(test_paid)[:300])

models = curl_json("https://openrouter.ai/api/v1/models")["data"]
free_models = []
for m in models:
    p = m.get("pricing", {})
    try:
        if float(p.get("prompt", 1)) == 0.0 and float(p.get("completion", 1)) == 0.0:
            free_models.append((m["id"], m.get("context_length", 0)))
    except Exception:
        pass

print(f"\n=== 2. FREE ($0) MODELS ON OPENROUTER ({len(free_models)}) ===")
for mid, ctx in sorted(free_models):
    print(f"  {mid:52s} | ctx={ctx}")

print("\n=== 3. DIGEST OF SCOUTED LEAN 4 CANDIDATES ===")
cands = json.loads((ROOT / "scouted_candidates.json").read_text(encoding="utf-8"))
print(f"Total Lean candidates loaded: {len(cands)}")

# Prioritize: (1) prize + 0 claims, (2) decidable/verifiable/falsifiable with low posts & 0 claims, (3) quiet open prize problems
scored = []
for c in cands:
    posts = c["forum"].get("posts", 0)
    claims = c["forum"].get("proof_claims", 0)
    has_prz = 1 if c["prize"] != "no" else 0
    is_fw = 1 if c["status"] in ("decidable", "verifiable", "falsifiable") else 0
    # Extract docstring or theorem part
    txt = c["lean_text"]
    # Clean copyright header
    body = re.sub(r"/-\s*Copyright.*?-/\s*", "", txt, flags=re.S).strip()
    scored.append((-(has_prz * 10 + is_fw * 5 - claims * 4 - posts * 0.3), c, body))

scored.sort(key=lambda x: x[0])
for rank, (_, c, body) in enumerate(scored[:22], 1):
    print(f"\n--- [{rank}] Problem #{c['number']} | status={c['status']} | prize={c['prize']} | posts={c['forum'].get('posts',0)} claims={c['forum'].get('proof_claims',0)} | tags={c['tags']} ---")
    print(body[:850])
