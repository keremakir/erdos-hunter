import json
import subprocess
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import yaml

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
    if res.returncode != 0:
        raise RuntimeError(f"curl error {res.returncode}: {res.stderr}")
    return json.loads(res.stdout)


def check_openrouter():
    print("=== OPENROUTER KEY & CREDITS ===")
    try:
        key_info = curl_json("https://openrouter.ai/api/v1/key", timeout=20)
        print("Key Info:", json.dumps(key_info, indent=2))
    except Exception as e:
        print("Key check error:", e)

    try:
        credits = curl_json("https://openrouter.ai/api/v1/credits", timeout=20)
        print("Credits Info:", json.dumps(credits, indent=2))
    except Exception as e:
        print("Credits check error:", e)

    try:
        models = curl_json("https://openrouter.ai/api/v1/models", timeout=25)["data"]
        print(f"Total OpenRouter models: {len(models)}")
        prefixes = ("deepseek/", "openai/", "anthropic/", "google/", "qwen/", "x-ai/", "moonshotai/")
        keywords = ("r1", "v3", "gpt-5", "o3", "o4", "claude", "gemini-2.5", "gemini-3", "qwen3", "qwq", "grok-3", "grok-4", "kimi")
        picked = []
        for m in models:
            mid = m["id"]
            if mid.startswith(prefixes) and any(k in mid.lower() for k in keywords):
                p = m.get("pricing", {})
                try:
                    inp = float(p.get("prompt", 0)) * 1e6
                    out = float(p.get("completion", 0)) * 1e6
                except Exception:
                    inp, out = 0.0, 0.0
                picked.append((mid, inp, out, m.get("context_length", 0)))
        print("\n=== AVAILABLE FRONTIER REASONING / MATH MODELS ===")
        for mid, inp, out, ctx in sorted(picked):
            print(f"  {mid:48s} | in=${inp:6.2f}/M | out=${out:6.2f}/M | ctx={ctx}")
    except Exception as e:
        print("Models list error:", e)


def fetch_lean_file(num):
    url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/{num}.lean"
    cmd = ["curl.exe", "-4", "-sS", "-f", "--max-time", "12", url]
    res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    return res.stdout if res.returncode == 0 and res.stdout.strip() else None


def scout_problems():
    yaml_path = Path(r"C:\Users\Kerem\.gemini\antigravity\brain\d05eb33c-51dc-4395-9d03-26b886d4c0a4\scratch\problems.yaml")
    data = yaml.safe_load(yaml_path.read_text(encoding="utf-8"))
    closed = {"proved", "proved (Lean)", "disproved", "disproved (Lean)", "solved", "solved (Lean)", "independent", "not provable", "not disprovable"}
    open_p = [p for p in data if p["status"]["state"] not in closed]

    fw = [p for p in open_p if p["status"]["state"] in ("falsifiable", "verifiable", "decidable")]
    print(f"\n=== ALL {len(fw)} FINITE-WITNESS PROBLEMS ===")
    for p in fw:
        f = p.get("forum", {})
        print(
            f"  #{str(p['number']):>4s} | {p['status']['state']:11s} | prz={str(p.get('prize','no')):6s} "
            f"| lean={p['formalized']['state']:3s} | posts={f.get('posts',0):2d} claims={f.get('proof_claims',0)} | tags={p.get('tags',[])}"
        )

    # Select all 46 finite-witness problems + 15 low-activity open formalized problems (number theory / combinatorics / graph theory)
    candidates = list(fw)
    low_hanging_open = sorted(
        [
            p for p in open_p
            if p["status"]["state"] in ("open", "open (Lean)")
            and p["formalized"]["state"] == "yes"
            and p.get("forum", {}).get("proof_claims", 0) == 0
            and p.get("forum", {}).get("posts", 0) <= 2
        ],
        key=lambda x: (0 if x.get("prize", "no") != "no" else 1, x.get("forum", {}).get("posts", 0), int(x["number"])),
    )
    print(f"\nTotal quiet open formalized problems (0 proof claims, <=2 posts): {len(low_hanging_open)}")
    candidates.extend(low_hanging_open[:20])

    out_lean_dir = ROOT / "lean_statements"
    out_lean_dir.mkdir(parents=True, exist_ok=True)
    summary = []

    with ThreadPoolExecutor(max_workers=12) as ex:
        fut_map = {ex.submit(fetch_lean_file, str(p["number"])): p for p in candidates}
        for fut in as_completed(fut_map):
            p = fut_map[fut]
            num = str(p["number"])
            txt = fut.result()
            if txt:
                (out_lean_dir / f"{num}.lean").write_text(txt, encoding="utf-8")
                summary.append({
                    "number": num,
                    "status": p["status"]["state"],
                    "prize": p.get("prize", "no"),
                    "tags": p.get("tags", []),
                    "forum": p.get("forum", {}),
                    "lean_text": txt,
                })

    summary.sort(key=lambda x: int(x["number"]))
    (ROOT / "scouted_candidates.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Fetched {len(summary)}/{len(candidates)} official Lean 4 statement files!")


if __name__ == "__main__":
    check_openrouter()
    scout_problems()
