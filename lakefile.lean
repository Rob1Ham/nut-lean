import Lake
open Lake DSL

/-!
# `cashu-lean` package

A zero-dependency Lean 4 model of the accounting core of a basic Cashu mint.
No mathlib, no FFI, no executable binary. The library root is
`CashuLean.lean`.
-/

package «cashu-lean» where
  description := "A Lean 4 formal model of basic Cashu mint accounting"

@[default_target]
lean_lib CashuLean where
  -- Root module `CashuLean.lean` transitively imports every submodule.
