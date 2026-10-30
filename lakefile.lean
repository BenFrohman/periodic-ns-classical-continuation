import Lake
open Lake DSL

package «PeriodicNSContinuation» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require FeffermanClayNS from git
  "https://github.com/BenFrohman/fefferman-clay-navier-stokes.git" @ "ebcf10921e02350e46b32b3bcded8dd8ca2c87c4"

@[default_target]
lean_lib «PeriodicNSContinuation» where
  roots := #[`PeriodicNSContinuation]
