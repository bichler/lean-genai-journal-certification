# Lean supplement: *Certification under Cheap Generation*

This is a Lean 4 / Mathlib formalization of the mathematical results in the
article. It is deliberately split into small modules so that the assumptions
behind every result are visible in the Infoview.

## Build it in VS Code

1. Install the **Lean 4** extension for VS Code.
2. Open this folder (not merely an individual `.lean` file) in VS Code.
3. In the integrated terminal, run:

   ```powershell
   lake update
   lake exe cache get
   lake build
   ```

4. Open `CertificationLean.lean`. Lean's Infoview checks every imported
   theorem as you open the file.

The project pins Lean `v4.36.0-rc2` and the corresponding Mathlib revision in
`lake-manifest.json`. The cache step only saves time; it does not change the
logical content of the proof.

## File map

| Article result | Lean module | Scope of the current formalization |
|---|---|---|
| Lemma 1 (optimal effort) | `Core.lean` | fully proved: FOCs, global optimum, output and utility formula |
| Proposition 1 | `Core.lean` | fully proved: difference identity, iff condition, sufficient order case |
| Corollary 1 | `Core.lean` | fully proved under the shared-screen and positive-credibility hypotheses |
| Propositions 2--4 | `CheapGeneration.lean` | quotient-rule normal forms, signs, and threshold/cutoff algebra; the raw `HasDerivAt` instantiation is isolated as a next step |
| Lemmas 2--3 | `Screening.lean` | review-frontier and net-capacity identities fully proved as real-algebra statements |
| Propositions 5--6 | `Screening.lean` | complementarity signs and triage-ratio identities; derivative/elasticity inputs remain explicit contracts |
| Proposition 7 | `Participation.lean` | generic fixed-point uniqueness and comparative-static order kernels under explicit response contracts |
| Proposition 8 | `Participation.lean` | collapse, high-crossing, and downward-closed threshold kernels; concrete greatest-branch regularity remains an explicit contract |
| Proposition 9 | `Aggregate.lean` | aggregate-derivative and tail-selection implications under explicit calculus/tail-mean contracts |

## What Lean proves and what must be instantiated

The algebraic claims and order arguments are stated directly and proved without
`sorry`, `admit`, or theorem-level axioms. Some economic results necessarily
need regularity hypotheses that the manuscript leaves abstract: differentiability
of generation responses, continuity and monotonicity of a submission CDF,
boundary conditions for best responses, and a tail-mean property of the
capability distribution. The corresponding Lean modules make these hypotheses
explicit rather than silently assuming them. The table above deliberately
separates a fully formal proof from a formal implication whose regularity input
still has to be instantiated from a chosen CDF or generation function.

Thus, a successful `lake build` verifies the article's formal conclusions
*conditional on exactly the assumptions shown in the theorem signatures*.
It does not test empirical claims or decide whether the assumptions are
substantively plausible.

## Suggested workflow for extending the supplement

Start with `Core.lean`, which has only real-algebra assumptions. Then replace
the abstract differentiability and response contracts in the other modules with
lemmas for a specific CDF (for example, a uniform or logistic capability
distribution). Lean will then check the full chain from that concrete choice
to the article's comparative statics.
