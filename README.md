# Classical Lottery in Action — Lean Artifact

This repository is the reviewer-facing landing page for the Classical Lottery artifact.

If you only want the paper, open [ClassicalLotteryInAction_companion.pdf](./ClassicalLotteryInAction_companion.pdf).

The repository contains the Lean 4 / Mathlib formalization of:

- Jingyuan Li, Ilia Tsetlin, Fan Wang, *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*;
- the companion Wakker--Debreu--Koopmans mechanization centered on additive representation and concavity transfer.

## Current status

This artifact is **complete, end-to-end**:

- the topology-side chain `T1–T6` is discharged;
- the construction-side chain `A4 → A1 → A3 → A2 → B → C` is discharged;
- `WakkerDebreuKoopmans.lean` closes the Wakker IV.2.7 / Debreu--Koopmans route from Wakker's six structural axioms;
- `Wakker/AxiomCheck.lean` is the one-file reviewer regression for the public theorem surface;
- every public theorem in the artifact audits only `[propext, Classical.choice, Quot.sound]`.

## Public-facing files

| File | Purpose |
| --- | --- |
| `ClassicalLotteryInAction_companion.pdf` | PDF companion giving the integrated overview of the Classical Lottery artifact and the Wakker--Debreu--Koopmans layer. |
| `ClassicalLotteryInAction.lean` | Main classical-lottery formalization: domain, axioms, smooth representation path, and ambiguity proposition. |
| `WakkerDebreuKoopmans.lean` | Thin re-export barrel preserving the stable import path for the split Wakker / Debreu--Koopmans mechanization. |
| `WakkerDebreuKoopmans/*.lean` | Reviewer-sized split proof modules: core, certificates, M2 frontier, construction stack, topology, closure, and audit. |
| `Wakker/AxiomCheck.lean` | One-file public axiom regression printing the headline theorem surface. |

## Minimal verification

From the repository root:

- `lake build WakkerDebreuKoopmans`
- `lake build Wakker.AxiomCheck`
- `lake build ClassicalLotteryInAction`

The root `lakefile.lean` exposes the artifact as a standalone Lean project and includes the reviewer regression root `Wakker.AxiomCheck`.

## Running code in Lean Web Editor

If you want a quick browser-based check without installing Lean locally, you can use the [Lean Web Editor](https://live.lean-lang.org/).

The easiest entry point for the browser editor is `ClassicalLotteryInAction.lean`:

1. Open the Lean Web Editor.
2. Copy the contents of `ClassicalLotteryInAction.lean` from this repository and paste them into the editor.
3. Wait for the Mathlib imports to finish loading.
4. Try a few quick checks such as:

   ```lean
   #check ClassicalLottery.prop_average_utility
   #check ClassicalLottery.thm_smooth_model
   #check ClassicalLottery.matching_freq_smooth_formula
   #check ClassicalLottery.prop_aversion_or_seeking
   ```

This browser workflow is best for quick inspection of the main standalone file. The split Wakker--Debreu--Koopmans stack (`WakkerDebreuKoopmans.lean`, `Wakker/AxiomCheck.lean`, and the files under `WakkerDebreuKoopmans/`) uses local multi-file imports, so it is better run in a local Lean project with the `lake build ...` commands listed above.

## Where to start

If you want the quickest reviewer pass:

1. Open `ClassicalLotteryInAction_companion.pdf`.
2. Run `lake build Wakker.AxiomCheck` to see the public kernel-axiom audit.
3. Open `WakkerDebreuKoopmans.lean`, then follow the split files under `WakkerDebreuKoopmans/`.
4. Read `ClassicalLotteryInAction.lean` for the Management Science-facing theorem surface.
