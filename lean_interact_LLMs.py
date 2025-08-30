#!/usr/bin/env python3
"""
lean_proof_loop.py (v3.5 live)
- Two-block merge + your custom prompt
- Endpoint-aware (Responses for o1/o3; Chat Completions for others)
- Improved Responses API text extraction (handles output_text and outputs[].content[].text.value forms)
- Logs initial system+user messages into conversation.jsonl
- Safe JSONL logging (coerces non-serializable objects to strings)
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple

try:
    from openai import OpenAI
except Exception as e:
    print("ERROR: Failed to import OpenAI SDK. Please `pip install -U openai`.", file=sys.stderr)
    raise

try:
    from lean_interact import LeanREPLConfig, LeanServer, Command
except Exception as e:
    print("WARNING: `lean_interact` not importable right now. Running requires that package.", file=sys.stderr)

try:
    from tqdm import tqdm
except Exception:
    tqdm = None


def load_env_variables():
    """
    Manually loads environment variables from a `.env` file located in the same directory as this script.
    """
    env_path = Path(__file__).resolve().parent / ".env"

    if not env_path.exists():
        raise FileNotFoundError(f".env file not found at {env_path}")

    with env_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue  # skip comments and blank lines
            if "=" not in line:
                continue  # skip malformed lines
            key, value = line.split("=", 1)
            os.environ[key.strip()] = value.strip()

    return {key: os.environ[key] for key in os.environ if key in open(env_path).read()}


env_vars = load_env_variables()
api_key = os.environ.get("api_key")

def read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8")

def write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")

def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")

CODE_BLOCK_RE = re.compile(r"```(?:\s*lean)?\s*(?P<code>[\s\S]*?)\s*```", re.IGNORECASE)

def extract_lean_blocks(text: str) -> List[str]:
    blocks = []
    for m in CODE_BLOCK_RE.finditer(text):
        code = m.group("code")
        if code.strip():
            blocks.append(code)
    return blocks

@dataclass
class LeanError:
    message: str
    severity: str
    line: Optional[int] = None
    col: Optional[int] = None
    end_line: Optional[int] = None
    end_col: Optional[int] = None
    codeframe: Optional[str] = None

def make_codeframe(code: str, line: int, col: int, end_line: Optional[int]=None, end_col: Optional[int]=None, context: int=2) -> str:
    lines = code.splitlines()
    i0 = max(1, line - context)
    i1 = min(len(lines), (end_line or line) + context)
    out = []
    for i in range(i0, i1 + 1):
        prefix = f"{i:>5} | "
        out.append(prefix + lines[i-1])
        if i == line:
            caret_line = " " * (len(prefix) + max(0, col-1)) + "^"
            if end_line == line and end_col and end_col > col:
                caret_line = " " * (len(prefix) + max(0, col-1)) + "^" * max(1, end_col - col)
            out.append(caret_line)
    return "\n".join(out)

def parse_pos_from_text(msg: str) -> Tuple[Optional[int], Optional[int]]:
    m = re.search(r"[Ll]ine\s+(\d+).{0,10}[Cc]ol(?:umn)?\s+(\d+)", msg)
    if m:
        return int(m.group(1)), int(m.group(2))
    return None, None

def run_lean_and_collect_errors(lean_code: str) -> List[LeanError]:
    try:
        config = LeanREPLConfig(verbose=False)
        server = LeanServer(config=config)
        response = server.run(Command(cmd=lean_code))
    except Exception as e:
        return [LeanError(message=f"[Runner] Failed to run Lean: {e}", severity="error")]

    errs: List[LeanError] = []
    for m in getattr(response, "messages", []):
        sev = getattr(m, "severity", "info")
        if sev not in ("error", "warning"):
            continue
        data = getattr(m, "data", "") or str(m)

        pos = getattr(m, "pos", None)
        endpos = getattr(m, "endPos", None)
        if isinstance(pos, dict):
            line = pos.get("line")
            col = pos.get("column") or pos.get("col")
        else:
            line = getattr(pos, "line", None) if pos else None
            col = getattr(pos, "column", None) if pos else None

        if isinstance(endpos, dict):
            end_line = endpos.get("line")
            end_col = endpos.get("column") or endpos.get("col")
        else:
            end_line = getattr(endpos, "line", None) if endpos else None
            end_col = getattr(endpos, "column", None) if endpos else None

        if line is None or col is None:
            line, col = parse_pos_from_text(data)

        codeframe = None
        if line is not None and col is not None:
            try:
                codeframe = make_codeframe(lean_code, line, col, end_line, end_col)
            except Exception:
                pass

        errs.append(LeanError(
            message=data, severity=sev, line=line, col=col, end_line=end_line, end_col=end_col, codeframe=codeframe
        ))
    return errs

def format_errors_for_llm(errs: List[LeanError], max_count: int = 6) -> str:
    if not errs:
        return "No errors."
    pieces = []
    for i, e in enumerate(errs[:max_count], 1):
        loc = ""
        if e.line is not None and e.col is not None:
            loc = f"(line {e.line}, col {e.col})"
        pieces.append(f"Error {i} {loc}:\n{e.message.strip()}")
        if e.codeframe:
            pieces.append("Codeframe:\n" + e.codeframe)
    if len(errs) > max_count:
        pieces.append(f"... and {len(errs) - max_count} more.")
    return "\n\n".join(pieces)

KNOWLEDGE_SENTINEL_RE = re.compile(r"^[ \t]*--[ \t]*knowledge axioms[ \t]*--[ \t]*$", re.MULTILINE)
THEOREM_RE = re.compile(r"(^|\n)[ \t]*(theorem|theorems)\b", re.IGNORECASE)

def insert_knowledge_and_proof(base_code: str, knowledge_block: str, proof_block: str) -> str:
    code = base_code
    if KNOWLEDGE_SENTINEL_RE.search(code):
        code = KNOWLEDGE_SENTINEL_RE.sub(knowledge_block.rstrip(), code, count=1)
    else:
        imports, others = [], []
        for line in code.splitlines():
            (imports if line.strip().startswith("import ") else others).append(line)
        code = ("\n".join(imports) + "\n" + knowledge_block.rstrip() + "\n" + "\n".join(others)).strip("\n") + "\n"

    m = None
    for m_ in THEOREM_RE.finditer(code):
        m = m_
    if m:
        start = m.start() if m.group(1) == "" else m.end()
        prefix, suffix = code[:start], code[start:]
        idx = suffix.find("sorry")
        if idx != -1:
            suffix = suffix[:idx] + proof_block.rstrip() + suffix[idx + len("sorry"):]
            code = prefix + suffix
        else:
            code = code.rstrip() + "\n\n-- (Note) No `sorry` found after last theorem; appended proof below:\n" + proof_block.rstrip() + "\n"
    else:
        code = code.rstrip() + "\n\n-- (Note) No `theorem` found; appended proof below:\n" + proof_block.rstrip() + "\n"
    return code

def default_system_prompt() -> str:
    return (
        "You are a Lean 4.3.0 proof assistant. You may include brief natural-language reasoning.\n"
        "However, your final answer must end with **two fenced ```lean code blocks** in order:\n"
        "  (1) knowledge axioms block, then (2) final proof block.\n"
        "If you include any other code blocks, ensure the **last two** are these answer blocks.\n"
        "Inside the code blocks, include only Lean code (no prose)."
    )

def default_task_prompt(lean_code: str) -> str:
    cheat_sheet = (
        "Cheat sheet for reading the code:\n"
        "1. Roles enum:\n"
        "   The helper macro `#genRoleTag` expands inductive types for RoleTags dynamically.\n"
        "   Example: `#genRoleTag PAG, POSSESSIVE, PART, PPT` expands to\n"
        "   `inductive RoleTag | PAG | POSSESSIVE | PART | PPT`.\n\n"
        "2. Uniform triple:\n"
        "   We encode predicate–argument structure via\n"
        "   `structure RoleAssignment (E T) := (role : RoleTag) (event : E) (value : T)`.\n\n"
        "3. Helper macros (`#genRoleHelpers [...]`):\n"
        "   For every role R it creates two names:\n"
        "   - `r` (lower-case): `E → T → RoleAssignment E T` (constructor for the triple)\n"
        "   - `R` (upper-case): `RoleAssignment E T → E → T → Prop` (predicate asserting the triple)\n\n"
        "4. Reading an axiom:\n"
        "   - Lower-case (e.g., `pag`, `ppt`) creates a link ⟨role, event, argument⟩.\n"
        "   - Upper-case (e.g., `PAG`, `PPT`) asserts/matches that link.\n"
        "   Example:\n"
        "   ```lean\n"
        "   let ra := pag e x\n"
        "   PAG ra e x -- true by definition\n"
        "   ```\n"
        "Requirements & tips:\n"
        "1) Assume a closed-world model: anything not asserted in `ax_xv0` does not hold.\n"
        "   You may introduce new axioms capturing commonsense lexical entailments (e.g.,\n"
        "   `man → person`) to bridge gaps between `ax_xv0` and the target theorem. It is\n"
        "   often shorter to add such standalone axioms explicitly—feel free to do so.\n"
        "2) Use **Lean 4.3.0** syntax.\n"
        "3) A useful tactic pattern is to unfold the main axiom `ax_xv0` (or whatever the\n"
        "   main axiom is named) and `rcases` it to obtain all factual statements; relate\n"
        "   those to the target theorem as needed.\n"
        "4) You may think out loud briefly, but your **final answer must end with exactly two**\n"
        "   ```lean blocks: first the extra axioms, then the final proof replacing `sorry`.\n"
        "5) If you use any library-defined tactics, include the required `import` statements\n"
        "   at the **beginning of the extra-axioms block**.\n"
        "6) Prefer standard tactics from core Lean; avoid nonstandard community tactics by default.\n"
        "Task:\n"
        "Produce two Lean code blocks:\n"
        "  • Block #1 (knowledge axioms): replace the line `-- knowledge axioms --` in the file.\n"
        "  • Block #2 (final proof): replace the `sorry` that occurs **after the last `theorem`**.\n\n"
        "Lean file content (for reference):\n"
        "-----\n"
        f"{lean_code}\n"
        "-----"
    )
    return f"{cheat_sheet}"

def build_feedback_prompt(errors_str: str) -> str:
    return (
        "Your last answer did not typecheck in Lean. Here are the compiler errors:\n"
        "-----\n"
        f"{errors_str}\n"
        "-----\n"
        "Please correct the mistakes. You may include brief reasoning, but ensure your response\n"
        "ends with **two ```lean blocks** in order:\n"
        "  (1) knowledge axioms (to replace `-- knowledge axioms --`), then\n"
        "  (2) the final proof (to replace the `sorry` after the last theorem).\n"
        "Make sure any required imports are at the top of the axioms block."
    )

def make_openai_client(api_key: Optional[str]) -> OpenAI:
    key = api_key or os.environ.get("OPENAI_API_KEY") or os.environ.get("api_key")
    if not key:
        raise RuntimeError("No API key found. Set OPENAI_API_KEY or pass --api-key.")
    return OpenAI(api_key=key)

def model_family(model: str) -> str:
    m = (model or "").lower()
    if m.startswith("o1") or m.startswith("o3"):
        return "reasoning"
    return "chat"

def use_responses_api(model: str, force: str) -> bool:
    if force == "responses":
        return True
    if force == "chat":
        return False
    return model_family(model) == "reasoning"

def messages_to_prompt(messages: List[Dict[str, str]]) -> str:
    parts = []
    for msg in messages:
        role = msg.get("role", "user").upper()
        content = msg.get("content", "")
        parts.append(f"[{role}]\n{content}\n")
    return "\n".join(parts).strip()

def _to_dict(obj):
    for attr in ("model_dump", "model_dump_json", "to_dict"):
        if hasattr(obj, attr):
            try:
                val = getattr(obj, attr)()
                if isinstance(val, dict):
                    return val
                if isinstance(val, str):
                    try:
                        return json.loads(val)
                    except Exception:
                        pass
            except Exception:
                pass
    if hasattr(obj, "json"):
        try:
            return json.loads(obj.json())
        except Exception:
            pass
    return None

def _extract_text_from_dict(d: dict) -> Optional[str]:
    for key in ("output_text", "text"):
        v = d.get(key)
        if isinstance(v, str) and v.strip():
            return v
    outputs = d.get("outputs") or d.get("output") or []
    if isinstance(outputs, dict):
        outputs = [outputs]
    texts = []
    for out in outputs:
        content = out.get("content") or []
        if isinstance(content, dict):
            content = [content]
        for c in content:
            t = c.get("text")
            if isinstance(t, str) and t.strip():
                texts.append(t)
            elif isinstance(t, dict):
                val = t.get("value")
                if isinstance(val, str) and val.strip():
                    texts.append(val)
    if texts:
        return "\n".join(texts)
    choices = d.get("choices")
    if isinstance(choices, list) and choices:
        msg = choices[0].get("message") or {}
        ct = msg.get("content")
        if isinstance(ct, str) and ct.strip():
            return ct
    return None

def responses_create_text(client: OpenAI, model: str, messages: List[Dict[str, str]], **kwargs) -> str:
    params = dict(kwargs)
    if "max_tokens" in params and "max_output_tokens" not in params:
        params["max_output_tokens"] = params.pop("max_tokens")
    params.pop("temperature", None)
    prompt = messages_to_prompt(messages)
    resp = client.responses.create(model=model, input=prompt, **params)
    for attr in ("output_text", "text"):
        if hasattr(resp, attr):
            raw = getattr(resp, attr)
            if isinstance(raw, str) and raw.strip():
                return raw
            val = getattr(raw, "value", None)
            if isinstance(val, str) and val.strip():
                return val
    d = _to_dict(resp) or {}
    s = _extract_text_from_dict(d)
    if s:
        return s
    return str(resp)

def chat_completions_create_text(client: OpenAI, model: str, messages: List[Dict[str, str]], **kwargs) -> str:
    return client.chat.completions.create(model=model, messages=messages, **kwargs).choices[0].message.content

def chat_once(client: OpenAI, model: str, messages: List[Dict[str, str]], force_endpoint: str = "auto", max_retries: int = 3, **kwargs) -> str:
    last_exc = None
    for attempt in range(1, max_retries + 1):
        try:
            if use_responses_api(model, force_endpoint):
                return responses_create_text(client, model, messages, **kwargs)
            else:
                return chat_completions_create_text(client, model, messages, **kwargs)
        except Exception as e:
            last_exc = e
            time.sleep(min(2 ** attempt, 5))
    raise last_exc

@dataclass
class RoundRecord:
    round_idx: int
    assistant_raw: str
    extracted_blocks: List[str]
    merged_code_path: str
    errors: List[Dict[str, Any]]

def run_loop(
    lean_file: Path,
    rounds: int,
    model: str,
    run_dir: Path,
    temperature: float = 0.2,
    max_tokens: int = 2000,
    api_key: Optional[str] = None,
    force_endpoint: str = "auto",
) -> Dict[str, Any]:

    run_dir.mkdir(parents=True, exist_ok=True)
    logs_dir = run_dir / "logs"
    logs_dir.mkdir(exist_ok=True)

    convo_path = logs_dir / "conversation.jsonl"
    errors_path = logs_dir / "errors.jsonl"
    config_path = run_dir / "config.json"
    final_path = run_dir / "final.lean"

    base_code = read_text(lean_file)
    client = make_openai_client(api_key)

    config = {
        "timestamp": now_iso(),
        "lean_file": str(lean_file),
        "rounds": rounds,
        "model": model,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "force_endpoint": force_endpoint,
    }
    write_text(config_path, json.dumps(config, indent=2))

    messages = [
        {"role": "system", "content": default_system_prompt()},
        {"role": "user", "content": default_task_prompt(base_code)},
    ]

    def _safe(obj: Any):
        try:
            json.dumps(obj)
            return obj
        except Exception:
            return str(obj)

    def log_convo(obj: Dict[str, Any]):
        safe_obj = {k: _safe(v) for k, v in obj.items()}
        with open(convo_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(safe_obj, ensure_ascii=False) + "\n")

    for m in messages:
        log_convo({"role": m["role"], "round": 0, "content": m["content"], "ts": now_iso()})

    def log_errors(round_idx: int, errs: List[LeanError]):
        with open(errors_path, "a", encoding="utf-8") as f:
            f.write(json.dumps({
                "round": round_idx,
                "errors": [asdict(e) for e in errs],
                "ts": now_iso(),
            }, ensure_ascii=False) + "\n")

    seen_error_fingerprints = []
    records: List[RoundRecord] = []

    for r in range(1, rounds + 1):
        if tqdm:
            iter_obj = tqdm([r], desc=f"Round {r}/{rounds}", leave=True)
        else:
            iter_obj = [r]

        for _ in iter_obj:
            assistant_raw = chat_once(
                client, model, messages,
                force_endpoint=force_endpoint,
                temperature=temperature,
                max_tokens=max_tokens,
            )
            if not isinstance(assistant_raw, str):
                assistant_raw = str(assistant_raw)

            log_convo({"role": "assistant", "round": r, "content": assistant_raw, "ts": now_iso()})

            blocks = extract_lean_blocks(assistant_raw)
            if len(blocks) < 2:
                messages.extend([
                    {"role": "assistant", "content": assistant_raw},
                    {"role": "user", "content": "Please end your response with TWO ```lean code blocks: block #1 = knowledge axioms; block #2 = final proof. If other blocks appear, ensure the LAST TWO are these."},
                ])
                log_convo({"role": "user", "round": r, "content": "Please end your response with TWO ```lean code blocks: block #1 = knowledge axioms; block #2 = final proof. If other blocks appear, ensure the LAST TWO are these.", "ts": now_iso()})
                continue

            ax_block, pr_block = blocks[-2], blocks[-1]

            merged_code = insert_knowledge_and_proof(base_code, ax_block, pr_block)
            merged_path = run_dir / f"candidate_round_{r}.lean"
            write_text(merged_path, merged_code)

            errs = run_lean_and_collect_errors(merged_code)
            log_errors(r, errs)

            if not any(e.severity == "error" for e in errs):
                write_text(final_path, merged_code)
                records.append(RoundRecord(
                    round_idx=r,
                    assistant_raw=assistant_raw,
                    extracted_blocks=[ax_block, pr_block],
                    merged_code_path=str(merged_path),
                    errors=[asdict(e) for e in errs],
                ))
                return {
                    "status": "pass",
                    "rounds_used": r,
                    "final": str(final_path),
                    "run_dir": str(run_dir),
                    "records": [asdict(x) for x in records],
                }

            fp = (errs[0].message if errs else "NO_ERROR_TEXT")[:512]
            seen_error_fingerprints.append(fp)
            if len(seen_error_fingerprints) >= 3 and len(set(seen_error_fingerprints[-3:])) == 1:
                records.append(RoundRecord(
                    round_idx=r,
                    assistant_raw=assistant_raw,
                    extracted_blocks=[ax_block, pr_block],
                    merged_code_path=str(merged_path),
                    errors=[asdict(e) for e in errs],
                ))
                return {
                    "status": "fail",
                    "reason": "repeated_same_error",
                    "rounds_used": r,
                    "run_dir": str(run_dir),
                    "records": [asdict(x) for x in records],
                }

            err_str = format_errors_for_llm(errs, max_count=6)
            feedback = (
                "Fix the issues and resend. You may include brief reasoning, but ensure your response **ends with TWO** ```lean blocks:\n"
                "1) Axioms to replace `-- knowledge axioms --`\n"
                "2) Final proof to replace the `sorry` after the last theorem\n\n"
                "Errors:\n-----\n" + err_str + "\n-----"
            )
            messages.extend([
                {"role": "assistant", "content": assistant_raw},
                {"role": "user", "content": feedback},
            ])
            log_convo({"role": "user", "round": r, "content": feedback, "ts": now_iso()})

            records.append(RoundRecord(
                round_idx=r,
                assistant_raw=assistant_raw,
                extracted_blocks=[ax_block, pr_block],
                merged_code_path=str(merged_path),
                errors=[asdict(e) for e in errs],
            ))

    return {
        "status": "fail",
        "reason": "max_rounds_exhausted",
        "rounds_used": rounds,
        "run_dir": str(run_dir),
        "records": [asdict(x) for x in records],
    }

def main():
    parser = argparse.ArgumentParser(description="LLM x Lean (two-block) proof loop, v3.5 (live)")
    parser.add_argument("--lean-file", required=True, type=Path, help="Path to the Lean file")
    parser.add_argument("--rounds", type=int, default=5, help="Max feedback rounds")
    parser.add_argument("--model", type=str, default=os.environ.get("OPENAI_MODEL", "o1"), help="OpenAI model name")
    parser.add_argument("--run-dir", type=Path, default=Path("./runs"), help="Directory to store outputs")
    parser.add_argument("--temperature", type=float, default=0.2, help="Ignored for o1*/o3* reasoning models")
    parser.add_argument("--max-tokens", type=int, default=2000, help="Token cap (mapped per endpoint)")
    parser.add_argument("--api-key", type=str, default=None, help="Override API key; otherwise use OPENAI_API_KEY/env")
    parser.add_argument("--force-endpoint", choices=["auto","chat","responses"], default="auto", help="Debug override for which endpoint to use")
    args = parser.parse_args()

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = args.run_dir / f"{stamp}_{args.lean_file.stem}"
    run_dir.mkdir(parents=True, exist_ok=True)

    result = run_loop(
        lean_file=args.lean_file,
        rounds=args.rounds,
        model=args.model,
        run_dir=run_dir,
        temperature=args.temperature,
        max_tokens=args.max_tokens,
        api_key=args.api_key,
        force_endpoint=args.force_endpoint,
    )
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
