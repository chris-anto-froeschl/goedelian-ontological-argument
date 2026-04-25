# Formal Verification of Axiom-Free Gödelian Ontological Argument and Trinity Necessity Proof in Isabelle/HOL

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18919345.svg)](https://doi.org/10.5281/zenodo.18919345)

## 📌 Overview
This project reconstructs metaphysical arguments (the Ontological Argument and the structure of the Trinity) into the domain of computational formalization and machine verification. Utilizing **Isabelle/HOL** (a Higher-Order Logic theorem prover), it translates philosophical claims into precise, mechanically verifiable logical theories.

Specifically, it overcomes the ambiguities (e.g., subjective concepts like "positive properties" or "perfection") and the vulnerability to Modal Collapse found in traditional Gödel-style proofs. All such concepts have been replaced with **strictly structural and mathematical definitions (relational support networks and Cantorian size comparisons)**.

## ✨ Key Features & Methodology

* **Axiom-Free Foundation:**
    No additional user-level metaphysical or modal logic axioms (such as the S5 axiom system) are introduced. All results are derived exclusively through conservative definitional extensions within the base logic of HOL. The development is mechanically certified at the kernel level to be strictly "axiom-free."
* **H-Optimality (H_opt) and MaxNT:**
    The "Supreme Truth" is mathematically modeled not by arbitrary perfections, but as a node receiving **Maximal Non-Trivial Support (MaxNT)** within a relational network—capturing the concept of "a truth so certain that no greater certainty can be conceived."
* **Avoidance of Modal Collapse:**
    The framework explicitly avoids the modal collapse phenomenon (where all contingent truths collapse into necessity) commonly triggered by strong modal axioms. It preserves contingency while still yielding a satisfiable, non-vacuous model.

## 🚀 Core Verifications

1. **Internal Consistency:**
    Through a Flat-model interpretation, the Isabelle/HOL kernel verifies that the concept of H_opt is free of contradiction (satisfiable) and non-vacuous. This satisfies Leibniz's strict prerequisite that the supreme concept must first be demonstrated as logically possible.
2. **Structural Exclusion & The Necessity of the Trinity (N=3):**
    The system mathematically proves that attempting to ground truth in Singularity (N=1), strict Duality (N=2), or Multiplicity (N >= 4) inevitably results in logical inconsistency or informational vacuity (≈-collapse). Consequently, a mutually supporting **Triune structure (N=3) emerges as the unique, stable logical fixed point**.
3. **Definitional Finality Theorem:**
    The system mechanically proves that under the given definitions, it is strictly impossible to define or conceive of a truth "more certain" or structurally superior to a candidate satisfying H_opt.
4. **Computational Diagnostics (Nitpick Genuine Model):**
    Using the bounded finite-model search tool *Nitpick*, the framework identifies a genuine, non-vacuous satisfying model for the N=3 configuration (while reporting UNSAT for N=1, 2, and 4+ constraints).

## 🛠 Build Instructions

All theorems in this project have been checked by the Isabelle/HOL kernel. To reproduce the proofs in your local environment, follow these steps:

### Requirements
* **Isabelle Version:** Isabelle2025
* **Platform:** Windows x86_64 (Poly/ML 5.9.1) or a compatible OS.

### Build Command
Navigate to the project directory in your terminal and run the following command to build the proof session:
```bash
isabelle build -D .



