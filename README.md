# Square-free cyclic Fuglede: Lean formalization

_Formal proof companion to Jiahui Liang's “Spectral Sets Tile in Cyclic Groups of Square-Free Order”_

---

## 📋 What this repository contains

This project formalizes the statement that every nonempty spectral subset of a finite cyclic group of square-free order is a translational tile. It also formalizes the coprime prime-step descent theorem used in the proof, starting from the original finite sets and their Fourier orthogonality conditions.

The formal main theorem does **not assume rapid growth** of the prime factors. The descent theorem retains its stated assumptions: an odd prime `q`, a positive cofactor `H` coprime to `q`, and `q` not dividing the cardinality of the spectral pair.

This is a **selected-results formalization**, not a claim that every assertion in the paper has been formalized. In particular, the separately cited tile-to-spectral implication is outside its scope. See [verified scope and limitations](SCOPE.md).

中文简介：这是平方自由阶有限循环群论文的 Lean 证明配套代码。它让读者可以自行重跑主定理及关键降阶机制的机器核验；不代表论文所有附加结论、文献和原创性都获得机器认证。

## 🎯 Main entry points

| Paper result | Formal declaration | Source |
|---|---|---|
| Spectral sets tile, Theorem 1.1 | `checked_main_statement` | [Expanded statement](FugledeAudit/MainStatementCheck.lean) |
| Coprime prime-step descent, Theorem 1.3 | `automatic_prime_step_descent` | [Descent and lifting](FugledeAudit/ActualTilingLift.lean) |
| Ambient Gram eigenvector | `spectral_pair_residual_raw_gram_eigenvector` | [Integral Gram matrix](FugledeAudit/ActualIntegralGram.lean) |
| Unit invariance, Lemma 2.1 | `spectral_pair_unit_invariance`, `tiling_unit_invariance` | [Unit invariance](FugledeAudit/UnitInvariance.lean) |
| Hadamard consequence, Corollary 7.1 | `squarefree_hadamard_rows_columns_tile` | [Hadamard consequences](FugledeAudit/HadamardConsequences.lean) |

The definitions of spectral pairs and unique tiling are in [PaperStatements.lean](FugledeAudit/PaperStatements.lean). [StatementAudit.lean](StatementAudit.lean) checks the exported statements separately; [AxiomAudit.lean](AxiomAudit.lean) lists the proof dependencies of every named theorem in the project.

## 🔧 Reproduce the checks

Install Git and Lean's official version manager, [elan][elan]. Run the following commands in the repository directory. The toolchain and library revisions are pinned; do not run `lake update` when reproducing this release.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true StatementAudit.lean
lake env lean AxiomAudit.lean
lake env leanchecker --fresh --verbose FugledeAudit
```

For the automated audit, use PowerShell 7, available on Windows, Linux and macOS:

```powershell
pwsh -File verify.ps1 -ReplayImports
```

The script checks the pinned Lean/mathlib revisions, source hashes, every proof file with warnings treated as errors, the exported statements, and the axiom allowlist. `-ReplayImports` additionally replays the complete imported declaration closure in an initially empty Lean kernel environment. This uses Lean's own kernel, not a separately implemented external verifier.

The build uses the fixed mathlib cache. Replaying the imported declaration closure is not the same as rebuilding the entire mathlib library from source. The [GitHub workflow](.github/workflows/lean.yml) runs the scripted audit using the official Lean action.[^1]

Pinned versions: Lean `4.33.1`; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. See [runtime-lock.json](runtime-lock.json) and [lake-manifest.json](lake-manifest.json).

## 📚 Paper and citation

Author: **Jiahui Liang**, Independent Researcher.

Related paper: [Spectral Sets Tile in Cyclic Groups of Square-Free Order](https://doi.org/10.5281/zenodo.22085489). The formalization was matched to the local manuscript revision dated September 7, 2026; this repository does not update or replace the public paper record.

When citing the code, cite the repository and the exact release tag or commit used. [CITATION.cff](CITATION.cff) provides software citation metadata.[^2] The paper DOI is not a DOI for this software, and this release does not claim a separate software DOI.

## ⚠️ AI use and responsibility

OpenAI's ChatGPT and Codex provided substantive assistance with literature screening, manuscript organization and wording, proof auditing, and development and debugging of the Lean formalization. The proof terms are checked by Lean; an AI-generated assertion or a successful-looking log is not itself a proof.

The author remains responsible for the paper and for the correspondence between its mathematical statements and the formal definitions. This repository does not claim that a human independently checked every proof line, establish priority or novelty, or certify journal acceptance. Lean, mathlib and the other pinned dependencies are acknowledged as the underlying formalization infrastructure and retain their own licenses.

The code and documentation authored for this repository are provided under the [MIT License](LICENSE). This software license does not change the license of the related paper or of any third-party dependencies.

[elan]: https://github.com/leanprover/elan
[^1]: Lean project. “lean-action: GitHub action for standard CI in Lean projects.” https://github.com/leanprover/lean-action
[^2]: GitHub Docs. “About CITATION files.” https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files
