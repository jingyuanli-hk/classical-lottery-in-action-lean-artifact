# Classical Lottery in Action — Lean Artifact

This repository is the reviewer-facing landing page for the Classical Lottery artifact.

If you only want the paper, open [ClassicalLotteryInAction_companion.pdf](./ClassicalLotteryInAction_companion.pdf).

The repository contains the Lean 4 / Mathlib formalization of:

- Jingyuan Li, Ilia Tsetlin, Fan Wang, *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*;
- the companion Wakker--Debreu--Koopmans mechanization centered on additive representation and concavity transfer.

## Current status

**Verified (sorry-free, kernel-clean):**

- every public theorem on the audited surface (`Wakker/AxiomCheck.lean`) — `wakker_IV_2_7`, `debreu_koopmans_hard`, the `AdditiveRep` consumers, and the Management Science theorems `prop_average_utility`, `lem_gap_filling`, `thm_smooth_model`, `matching_freq_smooth_formula`, `prop_aversion_or_seeking` — audits only `[propext, Classical.choice, Quot.sound]`;
- the topology ladder `T1–T6` and the construction-side wiring `A4 → A1 → A3 → A2 → B → C` are discharged as machine-checked implications;
- no project-specific axioms appear in the audited surface, and there is no `sorry`.

**Honest scope (what "audits clean" does and does not mean):**

- `wakker_IV_2_7` is a *conditional* wrapper: it consumes the additive-representation construction as an explicit, clearly-labelled hypothesis (`hConstruct`). The clean audit therefore certifies the packaging and reduction layers — **not** a forward proof from the bare structural axioms. The same applies to `debreu_koopmans_hard` (via `hConcAll`).
- That deep construction is reduced to a *single* proven-necessary structural input (the cross-pair Thomsen / double-cancellation hexagon, equivalently the per-slice grid representation), with **both** links of the §IV.5 construction assembled end-to-end around it. That input is **machine-checked irreducible** from Wakker's ordinal axioms {coordinate independence + restricted solvability + Archimedean + topology} (a concrete model satisfies independence on every coordinate yet violates the hexagon), and a sound cardinal-grid companion discharges the same conclusion once a coordinate scale is supplied.
- See `ClassicalLotteryInAction_companion.pdf` for the full account, the certificate architecture, and the irreducibility analysis.

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

## Citation

> Jingyuan Li, Ilia Tsetlin, and Fan Wang.
> *A Kernel-Clean Lean Mechanization of Classical Lottery in Action
and the Wakker–Debreu–Koopmans Representation Layer*

Please also cite the Management Science paper:

> Jingyuan Li, Ilia Tsetlin, and Fan Wang (2026),
> *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*,
> Management Science. DOI: [10.1287/mnsc.2023.04202](https://doi.org/10.1287/mnsc.2023.04202) 
