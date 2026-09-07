# Formalization scope

_Version 0.1.0 · selected results, not a full-paper certification_

---

## 🎯 Included

- The square-free spectral-to-tiling main theorem, using nonempty finite sets, equal cardinalities and the actual standard character sums in `ZMod N`.
- The entire coprime prime-step descent statement: both projection maps are injective, the literal images form a spectral pair, and tilings lift on both sides.
- The bearing proof chain: actual Fourier unitarity; CRT pairing and cyclotomic transfer; sparse powers; constructed residual spaces; the ambient `m/q` eigenvector identity for an integral Gram matrix; integrality collapse; commuting projections; Fourier zeros; descent and square-free induction.
- Both directions of the unit-invariance lemma.
- The nonempty square Hadamard-submatrix consequence: the original row and column sets tile, and the submatrix order divides the ambient order.

## ⚠️ Not included

- The full compatible unitary coordinates for the regular representation and all the multiplicity formulas in Lemma 3.2.
- The full spectral table with all algebraic multiplicities in Lemma 4.1. The actual ambient eigenvector identity needed by the main proof is included.
- The external tile-to-spectral theorem cited for the reverse direction of Corollary 1.2. It has not been introduced as an additional assumption or mathematical axiom in the proved main theorem.
- Literature history, priority, novelty, citation completeness, authorship, or publication decisions.

These exclusions are not missing premises hidden inside the closed main theorem. The formal proof bypasses the need to output the full representation coordinates before deriving the residual eigenvector identity, but does not thereby certify those additional representation claims.

## 📚 Definitions and edge cases

The main theorem assumes a positive square-free modulus. Its spectral set is nonempty by definition. A tiling means that every element of the original group has exactly one ordered pair of summands from the set and a finite complement.

The descent theorem assumes `q` prime, `3 ≤ q`, `gcd(q,H)=1` and `q ∤ |A|`. No rapid-growth or prime-separation hypothesis is added. The even endpoint of square-free induction is handled separately, not by applying the odd-prime operator lemma at `q=2`.

The Hadamard result is stated for a nonempty square Fourier submatrix with the precise Gram identity. It does not assert a tiling result for an empty or arbitrary rectangular matrix.

## 🔧 What a passed check means

The script's `PASS_SELECTED_SCOPE` status means that the version-pinned build, fresh proof-source checks, statement checks and axiom allowlist passed. With `-ReplayImports`, it also requires successful kernel replay of the imported declaration closure. The allowed dependencies are `propext`, `Classical.choice`, and `Quot.sound`, or none.

The script always records `entirePaperVerified: false`. A formal proof certifies its written statement relative to the checked foundation; matching that statement to the paper still requires inspection. A build or workflow badge is not a journal review or a proof of originality.
