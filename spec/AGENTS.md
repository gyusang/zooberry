# Repository Guidelines

## Project Structure & Module Organization

- `Basic/`: foundational Coq libraries, domains, syntax, maps, lattices, CFG nodes, tactics, and shared data types.
- `ItvInput/`, `TntInput/`: analyzer-specific input semantics and abstract domains.
- `Proof/`: reusable proof infrastructure shared by analyzer proofs.
- `ItvProof/`, `TntProof/`: analyzer-specific proof entry points, including `AllProof.v`.
- `Gen/`: validation and extraction modules. `make *_ext` writes generated OCaml files to `../analyzer/extract/`.
- `_CoqProject`: canonical Coq load paths and file order for editor integration.

## Build, Test, and Development Commands

Run commands from `spec/`.

- `make basic`: compile foundational modules in `Basic/`.
- `make proof`: compile shared proof modules in `Proof/`.
- `make Itv_proof`: compile interval analyzer input, validator generation, and interval proofs.
- `make Tnt_proof`: compile taint analyzer input, validator generation, and taint proofs.
- `make Itv_ext` or `make Tnt_ext`: compile input modules, run `Gen/Extract.v`, and refresh extracted OCaml under `../analyzer/extract/`.
- `make clean`: remove Coq build products such as `.vo`, `.glob`, `.v.d`, `.aux`, and generated `Makefile.coq*` files.

The top-level `make` target is intentionally invalid and prints supported targets.

## Coding Style & Naming Conventions

Use existing Coq style: two-space indentation inside modules and definitions, compact proof scripts, and short tactic lines. Keep copyright headers on new `.v` files. Prefer established prefixes: `Dom*` for domains, `Sem*` for semantics, `Cor*` for correctness, and `Ext*` for extraction proofs.

Use `-R` roots already defined in Makefiles and `_CoqProject`; avoid ad hoc relative imports.

## Testing Guidelines

Proof checking is the test suite. Run the narrow target first, then the full analyzer target affected by the change. Examples: `make basic` after editing `Basic/*.v`; `make Itv_proof` after editing `ItvInput/`, `ItvProof/`, `Proof/`, or `Gen/`.

For extraction changes, run `make Itv_ext` or `make Tnt_ext` and inspect generated OCaml changes in `../analyzer/extract/`.

## Commit & Pull Request Guidelines

Git history uses short, capitalized imperative subjects such as `Fix build script`, `Revise Makefile`, and `Bump to coq 8.12.2`. Keep commit subjects concise and mention Coq or extraction scope when useful.

Pull requests should describe changed modules, proof targets run, extraction targets run, and generated OCaml effects. Link related issues. Include terminal output only for failures or non-obvious proof obligations.

## Security & Configuration Tips

Do not commit transient Coq artifacts. `make clean` before reviewing diffs. Treat `make *_ext` as a cross-directory write because it deletes and rewrites files in `../analyzer/extract/`.
