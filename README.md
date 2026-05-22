# Classical Lottery in Action — Lean artifact

This repository packages the Lean 4 artifact developed by the **paper authors** for:

> **Jingyuan Li, Ilia Tsetlin, and Fan Wang** (2026),
> *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*,
> **Management Science**, Articles in Advance, published online 15 May 2026.
> DOI: [10.1287/mnsc.2023.04202](https://doi.org/10.1287/mnsc.2023.04202)

The repository is intended to make the artifact citable and discoverable for the formal-methods community. It contains the two main Lean source files discussed in the paper, together with two PDF companions:

- `ClassicalLotteryInAction.lean` — the Management Science Lean artifact.
- `WakkerDebreuKoopmans.lean` — the imported Wakker / Debreu--Koopmans wrapper layer.
- `LeanCompanionClassicalLotteryInAction.pdf` — the short companion note focused on the named-bridge interface and axiom audit.
- `MechanizedDecisionTheoryWakkerDK.pdf` — the ongoing spin-out note on the deeper Wakker / Debreu--Koopmans certificate layer.

This standalone snapshot also adds a minimal `lean-toolchain` and `lakefile.lean` so that the Lean files can be built outside the larger research workspace.

## License

This repository is licensed under the Apache License 2.0. See [`LICENSE.txt`](LICENSE.txt).

## What is formalized here?

The Management Science artifact formalizes the local classical-lottery and matching-frequency infrastructure, together with the public theorem boundaries used in the paper. Its design is intentionally audit-friendly: the deep non-local representation-theoretic ingredients are exposed as **named bridge hypotheses**, rather than hidden behind opaque axioms.

A live Lean axiom audit of the public theorem surface reports only the standard foundations
`[propext, Classical.choice, Quot.sound]` for:

- `prop_average_utility`
- `lem_gap_filling`
- `thm_smooth_model`
- `matching_freq_smooth_formula`
- `prop_aversion_or_seeking`

## Section-by-section map

| Paper location | Lean realization | Notes |
| --- | --- | --- |
| Paper §2.1 **Setting** | `ClassicalLotteryInAction.lean` sections `§2.1 Setting` and `§2.1 Preference structure` | Defines classical lotteries, acts, preferences, prize lifting, and Axiom 1 (`WeakOrder`). |
| Paper §2.2 **Evaluating Classical Lottery** | `ClassicalLotteryInAction.lean`, theorem `prop_average_utility` | Average-utility characterization for classical lotteries. The easy direction is proved directly; the representation-theorem direction is exposed as `AverageUtilityHardDirection`. |
| Paper §2.3 **Classical Lottery to Gauge Unverifiable Uncertainty** | `ClassicalLotteryInAction.lean`, matching-frequency development and theorem `lem_gap_filling` | Formalizes two-prize matching frequencies and the gap-filling lemma. The reverse strict-separation step is exposed as `MatchingFrequencyStrictSeparation`. |
| Paper §2.4 **The Main Result** | `ClassicalLotteryInAction.lean`, theorems `thm_smooth_model` and `matching_freq_smooth_formula` | Formalizes the smooth-model wrapper theorem and the normalized two-prize smooth matching-frequency formula. Deep W/DK-style sufficiency/regularity and inverse-`ψ` identification remain explicit bridges. |
| Paper §2.5 **A Note on Model Elicitation** and Appendix §5.4 **Rational Matching Frequencies** | `ClassicalLotteryInAction.lean`, `§App.4 Solvability` | Encoded as Axiom 8 (`Solvability`) together with boundary lemmas about rational matching classical lotteries. |
| Paper §2.6 **Ambiguity Attitudes** | `ClassicalLotteryInAction.lean`, theorem `prop_aversion_or_seeking` | Formalizes the ambiguity-attitude proposition. The behavioral-to-curvature recovery direction is isolated as `AmbiguityAttitudeCurvatureBridge`. |
| Appendix proofs for Proposition 1 / Lemma 1 / Theorem 1 / Proposition 2 | Spread across `ClassicalLotteryInAction.lean` local lemmas and theorem wrappers | The artifact checks the theorem-level reductions and local arguments while keeping the genuinely non-local representation steps visibly parameterized. |
| Imported Wakker / Debreu--Koopmans layer | `WakkerDebreuKoopmans.lean` and `MechanizedDecisionTheoryWakkerDK.pdf` | This is the deeper certificate layer. The ongoing spin-out tracks named certificates such as `hConstruct`, `hglobal`, `haff`, `hConc`, and `hPairConc`. |
| Paper §3 **Illustration** and §4 **Conclusion** | Not separately mechanized in this compact repository snapshot | These sections remain part of the published paper’s economic exposition rather than separate Lean modules. |

## Running the Lean files locally

This snapshot is set up as a minimal standalone Lean project pinned to the same Lean version used in the source workspace.

### Prerequisites

- [elan](https://lean-lang.org/elan/) for Lean toolchain management
- Git

### Build steps

```text
git clone https://github.com/jingyuanli-hk/classical-lottery-in-action-lean-artifact.git
cd classical-lottery-in-action-lean-artifact
lake update
lake build
```

### Check individual files

```text
lake env lean ClassicalLotteryInAction.lean
lake env lean WakkerDebreuKoopmans.lean
```

If you open the repository in VS Code with the Lean extension installed, the files should typecheck directly after `lake update` finishes fetching the pinned Mathlib dependency.

## Running in Lean Web Editor

For quick inspection in the Lean Web Editor:

1. Open [https://live.lean-lang.org/](https://live.lean-lang.org/).
2. Ensure the editor is using Lean `v4.28.0-rc1` (the version recorded in `lean-toolchain`).
3. Paste the contents of either `ClassicalLotteryInAction.lean` or `WakkerDebreuKoopmans.lean` into the editor.
4. Let the editor fetch Mathlib if prompted.

This is best for browsing declarations or quick typechecking of a single file. For the reproducible project setup, use the local `lake` workflow above.

## Companion note and W/DK spin-out

- `LeanCompanionClassicalLotteryInAction.pdf` explains the public theorem surface, the named-bridge interface, and the axiom-audit table.
- `MechanizedDecisionTheoryWakkerDK.pdf` records the deeper Wakker / Debreu--Koopmans certificate program as ongoing work, without changing the stable public interface consumed by `ClassicalLotteryInAction.lean`.

## Citation

If you cite this repository, please also cite the published paper:

> Jingyuan Li, Ilia Tsetlin, and Fan Wang (2026), *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*, Management Science. DOI: [10.1287/mnsc.2023.04202](https://doi.org/10.1287/mnsc.2023.04202)
