"""
Erdős-Hunter Multi-Model AI + Deterministic Python Verifier Swarm
Models (OpenRouter):
  - Theorist Alpha: openai/gpt-5.4
  - Theorist Beta:  deepseek/deepseek-r1-0528
  - Constructor:    qwen/qwen3.8-max-0902
  - Chief Referee:  anthropic/claude-opus-5.5
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(r"C:\Users\Kerem\.gemini\antigravity\scratch\erdos-hunter")
ENV = dict(
    line.strip().split("=", 1)
    for line in (ROOT / ".env").read_text(encoding="utf-8").splitlines()
    if "=" in line and not line.startswith("#")
)
KEY = ENV["OPENROUTER_API_KEY"]

MODELS = {
    "deepseek_v32": {
        "id": "deepseek/deepseek-v3.2",
        "fallback": "nvidia/nemotron-3-nano-omni-30b-a3b-reasoning:free",
        "role": "Algebraic & Combinatorial Theorist",
        "in_per_m": 0.26,
        "out_per_m": 0.38,
    },
    "nemotron_550b": {
        "id": "nvidia/nemotron-3-ultra-550b-a55b:free",
        "fallback": "qwen/qwen3.7-flash",
        "role": "550B Deep Mathematical Prover",
        "in_per_m": 0.00,
        "out_per_m": 0.00,
    },
    "gemma4_31b": {
        "id": "google/gemma-4-31b-it:free",
        "fallback": "qwen/qwen3-coder-30b-a3b-instruct",
        "role": "Computational Construction & Search Algorithm Architect",
        "in_per_m": 0.00,
        "out_per_m": 0.00,
    },
    "referee_luna": {
        "id": "openai/gpt-5.6-luna-pro",
        "fallback": "deepseek/deepseek-v3.2",
        "role": "Adversarial Referee, Literature Auditor & Lead Synthesizer",
        "in_per_m": 0.20,
        "out_per_m": 1.20,
    },
}


class BudgetTracker:
    def __init__(self, max_usd: float, ledger_path: Path):
        self.max_usd = max_usd
        self.spent_usd = 0.0
        self.calls = []
        self.lock = threading.Lock()
        self.ledger_path = ledger_path

    def check(self):
        with self.lock:
            if self.spent_usd >= self.max_usd:
                raise RuntimeError(f"Budget cap reached: ${self.spent_usd:.4f} >= ${self.max_usd:.2f}")

    def record(self, model_key: str, problem_id: str, phase: str, usage: dict, elapsed: float):
        cfg = MODELS[model_key]
        in_tok = usage.get("prompt_tokens", 0)
        out_tok = usage.get("completion_tokens", 0)
        # Prefer OpenRouter reported cost if present, else compute from rates
        cost = usage.get("cost")
        if cost is None:
            cost = (in_tok * cfg["in_per_m"] + out_tok * cfg["out_per_m"]) / 1e6
        cost = float(cost)
        with self.lock:
            self.spent_usd += cost
            entry = {
                "ts": round(time.time(), 2),
                "problem": problem_id,
                "phase": phase,
                "model": cfg["id"],
                "in_tokens": in_tok,
                "out_tokens": out_tok,
                "cost_usd": round(cost, 5),
                "cum_usd": round(self.spent_usd, 5),
                "elapsed_sec": round(elapsed, 2),
            }
            self.calls.append(entry)
            self.ledger_path.write_text(
                json.dumps({"max_usd": self.max_usd, "total_spent_usd": round(self.spent_usd, 5), "calls": self.calls}, indent=2),
                encoding="utf-8",
            )
            print(f"  [$] #{problem_id} | {phase:10s} | {cfg['id']:28s} | +{cost:.4f}$ (cum=${self.spent_usd:.4f}) | {elapsed:.1f}s", flush=True)


def call_openrouter(model_key: str, messages: list, budget: BudgetTracker, problem_id: str, phase: str, max_tokens: int = 2400, timeout: int = 120) -> str:
    budget.check()
    cfg = MODELS[model_key]
    for attempt_id in [cfg["id"], cfg.get("fallback")]:
        if not attempt_id:
            break
        payload = {
            "model": attempt_id,
            "messages": messages,
            "max_tokens": max_tokens,
            "temperature": 0.3,
        }
        t0 = time.perf_counter()
        with tempfile.NamedTemporaryFile("w", suffix=".json", dir=str(ROOT), delete=False, encoding="utf-8") as tf:
            json.dump(payload, tf)
            tf_path = tf.name

        try:
            cmd = [
                "curl.exe", "-4", "-sS", "--max-time", str(timeout),
                "-X", "POST",
                "-H", f"Authorization: Bearer {KEY}",
                "-H", "Content-Type: application/json",
                "-H", "HTTP-Referer: https://localhost",
                "-H", "X-Title: Erdos-Hunter-Swarm",
                "--data-binary", f"@{tf_path}",
                "https://openrouter.ai/api/v1/chat/completions",
            ]
            res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
            elapsed = time.perf_counter() - t0
            if res.returncode != 0:
                continue
            data = json.loads(res.stdout)
            if "error" in data:
                print(f"  [!] {attempt_id} -> {data['error'].get('code')}: {str(data['error'].get('message',''))[:90]}", flush=True)
                continue
            usage = data.get("usage", {})
            budget.record(model_key, problem_id, phase, usage, elapsed)
            msg = data["choices"][0]["message"]
            content = msg.get("content") or ""
            reasoning = msg.get("reasoning") or ""
            if not content.strip() and reasoning.strip():
                content = reasoning
            return content
        except Exception as e:
            print(f"  [!] Exception on {attempt_id}: {e}", flush=True)
        finally:
            try:
                os.remove(tf_path)
            except OSError:
                pass
    return "[API_ERROR] All models failed"


def extract_and_run_python(response_text: str, run_dir: Path, tag: str, timeout_sec: int = 25) -> dict:
    blocks = re.findall(r"```python\s*(.*?)```", response_text, flags=re.S | re.I)
    if not blocks:
        return {"ran": False, "reason": "no_python_block"}

    # Pick the longest / main verification or search script
    code = max(blocks, key=len)
    script_path = run_dir / f"code_{tag}.py"
    script_path.write_text(code, encoding="utf-8")

    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, str(script_path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_sec,
            cwd=str(run_dir),
        )
        elapsed = time.perf_counter() - t0
        return {
            "ran": True,
            "exit_code": proc.returncode,
            "elapsed_sec": round(elapsed, 2),
            "stdout": proc.stdout[-2500:],
            "stderr": proc.stderr[-1000:],
            "script": str(script_path),
        }
    except subprocess.TimeoutExpired as te:
        out = (te.stdout.decode("utf-8", errors="replace") if isinstance(te.stdout, bytes) else (te.stdout or ""))[-1500:]
        return {
            "ran": True,
            "exit_code": -999,
            "elapsed_sec": timeout_sec,
            "stdout": out,
            "stderr": f"TIMEOUT after {timeout_sec}s",
            "script": str(script_path),
        }


ATTACK_SYS_PROMPT = """You are an elite research mathematician and computational combinatorics / number theory specialist working inside the Erdős-Hunter Swarm.
Rules:
1. ZERO HALLUCINATION: Never claim a theorem or bound without exact justification or computational check. If a partial result is already known in literature, state it honestly so we don't rediscover old papers.
2. You are given the official Lean 4 formal specification from google-deepmind/formal-conjectures. Read EVERY condition carefully (strict vs non-strict inequalities, floor/ceiling, edge cases).
3. Your output MUST contain:
   (A) **Mathematical Reduction & Novel Attack Angle** (<= 350 words): Exact reformulation, tightest known bounds, and a concrete way to either construct a counterexample/witness, prove a new finite barrier/case, or attack the full statement.
   (B) **Self-Contained Executable Python Script** (` ```python ... ``` `): Must run in <= 20 seconds using only Python stdlib + `numpy`, `scipy`, `networkx` (all pre-installed). It must test small/medium cases, run smart heuristic/tabu/algebraic/LP search, and **independently verify** any candidate witness/bound before printing clear numerical results!
"""

REFEREE_SYS_PROMPT = """You are the ruthless Chief Referee & Literature Auditor of the Erdős-Hunter Swarm.
You receive:
- The official Lean 4 specification of an open Erdős problem.
- Three independent mathematical & computational attacks (GPT-5.4, DeepSeek-R1, Qwen-3.8-Max) PLUS the ACTUAL stdout/stderr from running their Python scripts on a real machine!

Your job:
1. **Audit & Falsify**: Catch any misread quantifier (e.g. `2 * |V'| + 1 >= n` in Lean vs `|V'| >= n/2`), numerical bug, timeout, or rediscovery of already-known literature.
2. **Extract Verified Facts**: State what the Python runs ACTUALLY proved or discovered (exact small-n values, LP/Delsarte bounds, best construction scores, or counterexample proximity).
3. **Select the #1 Winning Lead & Write Upgraded Python Experiment**: Synthesize the strongest mathematical insight from all 3 agents and output ONE upgraded, bug-free ` ```python ... ``` ` script (<= 22s runtime, stdlib + `numpy`/`scipy`/`networkx`) to push that exact lead further right now!
"""


def solve_problem(problem_num: str, note: str, budget: BudgetTracker, session_dir: Path) -> dict:
    lean_path = ROOT / "lean_statements" / f"{problem_num}.lean"
    lean_code = lean_path.read_text(encoding="utf-8")
    p_dir = session_dir / f"problem_{problem_num}"
    p_dir.mkdir(parents=True, exist_ok=True)

    print(f"\n================ ATTACKING ERDŐS #{problem_num} ({note}) ================", flush=True)

    user_prompt = f"Target: Erdős Problem #{problem_num} ({note})\n\nOfficial Lean 4 Specification:\n```lean\n{lean_code}\n```\n\nExecute your mathematical reduction and write your self-contained Python search/verification script (<20s runtime)."

    attackers = ["deepseek_v32", "nemotron_550b", "gemma4_31b"]
    round1_results = {}

    def run_attacker(mkey):
        resp = call_openrouter(
            mkey,
            [{"role": "system", "content": ATTACK_SYS_PROMPT}, {"role": "user", "content": user_prompt}],
            budget,
            problem_num,
            f"R1-{mkey}",
            max_tokens=2300,
        )
        (p_dir / f"r1_{mkey}.md").write_text(resp, encoding="utf-8")
        exec_res = extract_and_run_python(resp, p_dir, f"r1_{mkey}", timeout_sec=22)
        return mkey, resp, exec_res

    with ThreadPoolExecutor(max_workers=3) as ex:
        futs = [ex.submit(run_attacker, mk) for mk in attackers]
        for f in as_completed(futs):
            mk, resp, exec_res = f.result()
            round1_results[mk] = {"response": resp, "exec": exec_res}
            print(f"  [Py] #{problem_num} | {mk:12s} | ran={exec_res.get('ran')} exit={exec_res.get('exit_code')} ({exec_res.get('elapsed_sec',0)}s)", flush=True)

    # Round 2: Chief Referee audits all 3 + runs upgraded synthesis script!
    ref_bundle = [f"Official Lean 4 File for Erdős #{problem_num}:\n```lean\n{lean_code}\n```\n"]
    for mk in attackers:
        r = round1_results[mk]
        ex_info = r["exec"]
        ref_bundle.append(
            f"=== AGENT {mk} ({MODELS[mk]['id']}) ===\n"
            f"{r['response'][:3000]}\n\n"
            f"--- ACTUAL PYTHON EXECUTION RESULT ({mk}) ---\n"
            f"Exit Code: {ex_info.get('exit_code')} | Time: {ex_info.get('elapsed_sec')}s\n"
            f"STDOUT:\n{ex_info.get('stdout','')}\n"
            f"STDERR:\n{ex_info.get('stderr','')}\n"
        )

    ref_resp = call_openrouter(
        "referee_luna",
        [{"role": "system", "content": REFEREE_SYS_PROMPT}, {"role": "user", "content": "\n\n".join(ref_bundle)}],
        budget,
        problem_num,
        "R2-referee",
        max_tokens=2400,
    )
    (p_dir / "r2_referee.md").write_text(ref_resp, encoding="utf-8")
    ref_exec = extract_and_run_python(ref_resp, p_dir, "r2_referee", timeout_sec=25)
    print(f"  [Py-Ref] #{problem_num} | referee_luna  | ran={ref_exec.get('ran')} exit={ref_exec.get('exit_code')} ({ref_exec.get('elapsed_sec',0)}s)", flush=True)

    summary = {
        "problem": problem_num,
        "note": note,
        "round1_exec": {mk: round1_results[mk]["exec"] for mk in attackers},
        "referee_exec": ref_exec,
        "referee_verdict_preview": ref_resp[:2200],
    }
    (p_dir / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-budget-usd", type=float, default=6.00)
    args = ap.parse_args()

    ts = time.strftime("%Y%m%d-%H%M%S")
    session_dir = ROOT / "swarm_runs" / ts
    session_dir.mkdir(parents=True, exist_ok=True)
    budget = BudgetTracker(max_usd=args.max_budget_usd, ledger_path=session_dir / "ledger.json")

    targets = [
        ("128", "$250 Prize | falsifiable | Triangle-free graph with dense >=n/2 induced subgraphs"),
        ("835", "verifiable | Johnson graph chromatic number J(2k,k)=k+1, k=10 next open frontier!"),
        ("552", "$100 Prize | open (0 claims) | C4-Star Ramsey number R(C4, S_n) <= n + sqrt(n) - c"),
        ("628", "falsifiable (0 claims) | Erdos-Lovasz Tihany Conjecture first open case (k=6, a=3, b=4)"),
    ]

    all_summaries = []
    # Run 2 problems concurrently to maximize speed without hitting rate limits
    with ThreadPoolExecutor(max_workers=2) as ex:
        fut_map = {ex.submit(solve_problem, num, note, budget, session_dir): num for num, note in targets}
        for fut in as_completed(fut_map):
            num = fut_map[fut]
            try:
                res = fut.result()
                all_summaries.append(res)
            except Exception as e:
                print(f"[!] Problem #{num} error: {e}", flush=True)

    all_summaries.sort(key=lambda x: int(x["problem"]))
    (session_dir / "campaign_report.json").write_text(json.dumps(all_summaries, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"\n=== SWARM WAVE 1 COMPLETE | Total Spend: ${budget.spent_usd:.4f} / ${budget.max_usd:.2f} ===")
    print(f"Session directory: {session_dir}")


if __name__ == "__main__":
    main()
