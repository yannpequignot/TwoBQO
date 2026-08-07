import Lake

open Lake DSL

/-!
# Lake configuration

The library tree under `NashWilliams/` mirrors the intended Mathlib paths: a file staged for
`Mathlib/Order/TwoBQO.lean` lives at `NashWilliams/Order/TwoBQO.lean`. Upstreaming is therefore a
`NashWilliams` → `Mathlib` prefix swap in paths and imports. (A literal top-level `Mathlib/`
directory is not usable here — it would shadow the Mathlib dependency.)
-/

require "leanprover-community" / "mathlib" @ git "v4.28.0"

/-- Mathlib's own build options, so this project is held to the same standard as the code it is
staged for. Mirrors `mathlibLeanOptions` in Mathlib's `lakefile.lean`; the linters are passed as
`weak.` so that they apply to `lake build` without entering the trace hash. -/
abbrev projectLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.longFile, .ofNat 1500⟩
]

package «NashWilliams» where
  leanOptions := projectLeanOptions

@[default_target]
lean_lib «NashWilliams» where
  leanOptions := projectLeanOptions
