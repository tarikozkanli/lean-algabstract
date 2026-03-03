# Contributing

Thanks for contributing to Algabstract.

## Development setup

1. Install `elan` (Lean version manager).
2. Clone the repository.
3. Run:

```bash
lake build
```

The pinned toolchain is defined in `lean-toolchain`.

## Project structure

- `Algabstract.lean`: root export module.
- `Algabstract/`: algebraic structure modules.
- `lakefile.lean`: package config.

## Contribution guidelines

- Keep changes focused and minimal.
- Preserve the hierarchy design and avoid redundant fields when inheritance already provides them.
- Add or update module-level documentation when introducing new structures.
- Ensure the project builds before opening a PR.

## Before opening a PR

Run:

```bash
lake build
```

If build artifacts or local cache issues occur, retry after:

```bash
lake clean
lake build
```
