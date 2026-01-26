import pytest
import json
from pathlib import Path
from hol4_mcp.hol_session import HOLSession, escape_sml_string

FIXTURES_DIR = Path("tests/fixtures").absolute()
SML_HELPERS_DIR = Path("hol4_mcp/sml_helpers").absolute()

@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    # Load tactic_prefix.sml
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()

async def get_step_plan(session: HOLSession, tactic: str):
    escaped = escape_sml_string(tactic)
    output = await session.send(f'step_plan_json "{escaped}";', timeout=10)
    # Output looks like: {"ok":"[{\"end\":10,\"cmd\":\"e(...)\"}]"}
    # We need to parse strict json.
    # The session output might contain other text?
    # Usually the helpers print distinct lines.
    
    # Simple parsing assuming the helper prints just the JSON line we want at the end
    lines = output.strip().split('\n')
    json_line = lines[-1]
    if json_line.startswith('val it ='): # PolyML output if it prints return value
        # Look for the printed output instead
        pass
        
    try:
        data = json.loads(json_line)
        if "ok" in data:
            return json.loads(data["ok"]) # The inner string is JSON
        if "err" in data:
            raise ValueError(f"SML error: {data['err']}")
    except json.JSONDecodeError:
        pass
        
    # fallback: scan for {"ok":...}
    for line in lines:
        try:
            val = json.loads(line)
            if "ok" in val:
                return json.loads(val["ok"])
        except:
            continue
            
    raise ValueError(f"Could not parse step_plan output: {output}")

@pytest.mark.asyncio
async def test_bracket_offset(hol_session):
    tactic = "(simp[])"
    plan = await get_step_plan(hol_session, tactic)
    print(f"\nTactic: '{tactic}' (len {len(tactic)})")
    print(f"Plan: {plan}")
    
    # We expect one step
    assert len(plan) == 1
    step = plan[0]
    
    # The end offset
    end_offset = step['end']
    print(f"Reported end offset: {end_offset}")
    
    # Hypothesis: end_offset corresponds to 'simp[]' end, excluding ')'
    # 'simp[]' is 6 chars. ')' is at index 7 (0-indexed). len is 8.
    # If end_offset is 7, it means it includes up to index 7 (exclusive? or inclusive?).
    # HOL often uses 1-based indexing for columns, check what tactic_prefix uses.
    # "sliceTacticBlock ... string size" usually implies 0-based indexing relative to string start?
    
    # Let's check with a simple atom first to establish baseline
    tactic_simple = "simp[]"
    plan_simple = await get_step_plan(hol_session, tactic_simple)
    print(f"Simple end: {plan_simple[0]['end']}")
    
    # If simple is 6, and bracketed is 7 (or 6), we know.
