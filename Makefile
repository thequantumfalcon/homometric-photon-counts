.DEFAULT_GOAL := help
PYTHON ?= python
.PHONY: help verify check test replay build release
help:
	@echo "verify/check: offline inventory and repository checks"
	@echo "test: exact standard-library replay into build/quick-check"
	@echo "replay: extended Arb replay into build/arb-check"
	@echo "build/release: create/execute a source artifact; never publish"
verify:
	$(PYTHON) tools/project.py verify
check:
	$(PYTHON) tools/project.py check
test:
	$(PYTHON) tools/project.py test --output build/quick-check
replay:
	$(PYTHON) tools/project.py replay --output build/arb-check
build:
	$(PYTHON) tools/project.py build --output dist/homometric-photon-counts-source.zip
release:
	$(PYTHON) tools/project.py release --output dist/homometric-photon-counts-source.zip
