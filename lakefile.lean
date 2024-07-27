import Lake
open Lake DSL

package «puzzles» where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

lean_lib «Puzzles» where
  -- add library configuration options here

@[default_target]
lean_exe «puzzles» where
  root := `Main

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.1.0"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git" @ "main"/"lean"
