import Lake
open Lake DSL

package "question1" where
  version := v!"0.1.0"

lean_lib «Question1» where
  -- add library configuration options here

@[default_target]
lean_exe "question1" where
  root := `Main
