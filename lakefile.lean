import Lake
open Lake DSL

package «PeriodicNSContinuation» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require FeffermanClayNS from git
  "https://github.com/BenFrohman/fefferman-clay-navier-stokes.git" @ "ebcf10921e02350e46b32b3bcded8dd8ca2c87c4"

require WeightedEnstrophy from git
  "https://github.com/BenFrohman/weighted-enstrophy-identities.git" @ "1df4652d1a40430055ba6480904db5ab270497c3"

require TorusFourierNS from git
  "https://github.com/BenFrohman/torus-fourier-ns-lemmas.git" @ "2356dcb502dcc90c79f9b418438ab6636130010c"

@[default_target]
lean_lib «PeriodicNSContinuation» where
  roots := #[`PeriodicNSContinuation]
