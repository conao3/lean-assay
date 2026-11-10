# Run the targets inside the dev shell: `nix develop -c make check`.

.PHONY: build test format format-check check

build:
	lake build Assay Examples

test: build
	lake test

format:
	treefmt

format-check:
	treefmt --ci

check: format-check test
