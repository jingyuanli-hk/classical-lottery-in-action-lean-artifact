import Lake
open Lake DSL

package «ClassicalLotteryLeanArtifact»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5bad60a0ca3c2a0db665304e78153ccdeb6d80b9"

@[default_target]
lean_lib ClassicalLotteryLeanArtifact where
  roots := #[`ClassicalLotteryInAction, `WakkerDebreuKoopmans]
