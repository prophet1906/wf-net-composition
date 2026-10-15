#!/usr/bin/env python3
"""
Top-level entry point for the Unified Fault Injection, Formal Repair & Channel Fusion Verification Pipeline.

Delegates directly to src.pipeline.main().
"""

import sys
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.pipeline import main

if __name__ == "__main__":
    sys.exit(main())
