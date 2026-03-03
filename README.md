# Algabstract

A Lean 4 library package for algebraic abstractions.

## Structures included

- Single operation hierarchy:
  - `Magma`
  - `Semigroup`
  - `Monoid`
  - `Group`
  - `AbelianGroup`
- Two operation hierarchy:
  - `Semiring`
  - `Ring`
  - `CommutativeRing`
  - `Field`

## Project layout

- `Algabstract.lean` — root export module
- `Algabstract/` — library modules
- `lakefile.lean` — Lake package configuration
- `lean-toolchain` — pinned Lean version

## Project metadata

- [LICENSE](LICENSE)
- [CONTRIBUTING](CONTRIBUTING.md)

## Build

```bash
lake build
```

## Clean

```bash
lake clean
```

## Use in another Lean project

Import the root module:

```lean
import Algabstract
```

Or import individual modules, for example:

```lean
import Algabstract.Field
```
