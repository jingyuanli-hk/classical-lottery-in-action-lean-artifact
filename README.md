# Classical Lottery in Action — Lean Artifact

This repository is the reviewer-facing landing page for the Classical Lottery artifact.
It contains the Lean 4 / Mathlib formalization of:

- Jingyuan Li, Ilia Tsetlin, Fan Wang, *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*;
- the companion Wakker--Debreu--Koopmans mechanization centered on additive representation and concavity transfer.

## Current status

As recorded in `WAKKER_COMPLETION_ROADMAP.md` (snapshot 2026-05-25), this artifact is **complete, end-to-end**:

- the topology-side chain `T1–T6` is discharged;
- the construction-side chain `A4 → A1 → A3 → A2 → B → C` is discharged;
- `WakkerDebreuKoopmans.lean` closes the Wakker IV.2.7 / Debreu--Koopmans route from Wakker's six structural axioms;
- `Wakker/AxiomCheck.lean` is the one-file reviewer regression for the public theorem surface;
- every public theorem in the artifact audits only `[propext, Classical.choice, Quot.sound]`.

## Key files

| File | Purpose |
| --- | --- |
| `ClassicalLotteryInAction.lean` | Main classical-lottery formalization: domain, axioms, smooth representation path, and ambiguity proposition. |
| `WakkerInfrastructure.lean` | Product-preference infrastructure and necessity-side Wakker lemmas. |
| `WakkerExistence.lean` | Grid-utility / standard-sequence entry point used by the Wakker construction side. |
| `WakkerDebreuKoopmans.lean` | Thin re-export barrel preserving the historical import path. |
| `WakkerDebreuKoopmans/*.lean` | Reviewer-sized split of the Wakker / Debreu--Koopmans mechanization: core, certificates, M2 frontier, construction stack, topology, closure, and audit. |
| `Wakker/AxiomCheck.lean` | One-file public axiom regression importing the detailed audit and printing the headline theorem surface. |
| `ClassicalLotteryInAction_companion.tex` | Merged formal-methods companion covering the main Classical Lottery artifact and the Wakker / Debreu--Koopmans layer. |
| `MechanizedDecisionTheoryWakkerDK.tex` | Formal-methods companion paper for the Wakker / DK layer. |
| `LeanCompanionClassicalLotteryInAction.tex` | Short Lean companion for the main Classical Lottery artifact. |
| `WAKKER_COMPLETION_ROADMAP.md` | Closure audit and certificate-history document. |

## Minimal verification

From the repository root:

- `lake build WakkerDebreuKoopmans`
- `lake build Wakker.AxiomCheck`
- `lake build ClassicalLotteryInAction`
- `latexmk -pdf -interaction=nonstopmode -halt-on-error "MechanizedDecisionTheoryWakkerDK.tex"`
- `latexmk -pdf -interaction=nonstopmode -halt-on-error "ClassicalLotteryInAction_companion.tex"`

The root `lakefile.lean` exposes the artifact as a standalone Lean project and includes the reviewer regression root `Wakker.AxiomCheck`.

## Where to start

If you want the quickest reviewer pass:

1. Read `MechanizedDecisionTheoryWakkerDK.tex` for the contribution and certificate architecture.
2. Read `ClassicalLotteryInAction_companion.tex` for the merged formal-methods overview of both artifact layers.
3. Run `lake build Wakker.AxiomCheck` to see the public kernel-axiom audit.
4. Check `WAKKER_COMPLETION_ROADMAP.md` for the closure audit.
5. Open `WakkerDebreuKoopmans.lean` for the module map, then follow the split files under `WakkerDebreuKoopmans/`.
