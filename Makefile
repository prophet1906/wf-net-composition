# =============================================================================
# Makefile for wf-net-composition Artifact
#
# Paper: Interface-Guided Discovery, Repair, and Verification of
#        Microservice Workflow Nets
# Authors: Shubham and Meenakshi D'Souza (IIIT Bangalore)
# =============================================================================

.PHONY: all proofs check rebuild check-env demo test benchmark-drift benchmark-partial clean help

all: proofs

proofs:
	@$(MAKE) -C proofs all

check:
	@$(MAKE) -C proofs check

rebuild:
	@$(MAKE) -C proofs rebuild

check-env:
	@python3 pipeline.py --check-env

demo:
	@python3 pipeline.py --demo

test:
	@python3 -m unittest discover tests

benchmark-drift:
	@python3 pipeline.py --benchmark drift

benchmark-partial:
	@python3 pipeline.py --benchmark partial

clean:
	@$(MAKE) -C proofs clean
	@rm -rf src/__pycache__ tests/__pycache__
	@rm -rf data/benchmarks/repaired
	@find . -type d -name "__pycache__" -exec rm -rf {} +
	@find . -type f -name "*.pyc" -delete
	@find . -type f -name ".DS_Store" -delete
	@echo "Cleaned build artifacts and cache files."

help:
	@echo "Available targets:"
	@echo "  make proofs             Compile formal Rocq proofs in proofs/"
	@echo "  make check              Validate proof terms using independent Rocq kernel checker (rocq check)"
	@echo "  make rebuild            Force clean re-compilation of proofs from scratch"
	@echo "  make check-env          Run environment pre-flight diagnostics (Python, PM4Py, LoLA, Graphviz)"
	@echo "  make demo               Run fast empirical verification demo (<60s) on representative defect tiers"
	@echo "  make test               Run Python unit test suite"
	@echo "  make benchmark-drift    Run evaluation across pure label drift benchmark suites"
	@echo "  make benchmark-partial  Run evaluation across pure truncation loss benchmark suites"
	@echo "  make clean              Remove build artifacts, compiled bytecode, and caches"
