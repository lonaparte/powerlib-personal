import Lake
open Lake DSL

package phdae where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PHDAE where
  srcDir := "."
