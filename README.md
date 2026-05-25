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

This repository intentionally presents the companion as a PDF artifact rather than a TeX source bundle.

## Minimal verification

From the repository root:

- `lake build WakkerDebreuKoopmans`
- `lake build Wakker.AxiomCheck`
- `lake build ClassicalLotteryInAction`

The root `lakefile.lean` exposes the artifact as a standalone Lean project and includes the reviewer regression root `Wakker.AxiomCheck`.

## Where to start

If you want the quickest reviewer pass:

1. Open `ClassicalLotteryInAction_companion.pdf`.
2. Run `lake build Wakker.AxiomCheck` to see the public kernel-axiom audit.
3. Open `WakkerDebreuKoopmans.lean`, then follow the split files under `WakkerDebreuKoopmans/`.
4. Read `ClassicalLotteryInAction.lean` for the Management Science-facing theorem surface.
