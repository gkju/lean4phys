# lean4phys

A study repository dedicated to learning interactive theorem proving in **Lean 4** and exploring the formalization of mathematical structures in physics.

The primary objective of this project is educational: bridging standard theoretical physics intuition (differential geometry, relativistic symmetries, and operator algebras) with the rigor of dependent type theory using [Mathlib](https://github.com/leanprover-community/mathlib4).

---

## Scope & Current Topics

Work in this repository is currently focused on the algebraic foundations of spacetime symmetries and spinor geometry:

* **Quadratic Forms & Clifford Algebras:** Formalizing generators, relations, and the universal property of $\mathcal{C}\ell(M, Q)$ using Mathlib's `LinearAlgebra.CliffordAlgebra`.
* **Involutions & $\mathbb{Z}_2$-Grading:** Grade involutions (parity), reversion (anti-automorphisms), Clifford conjugation, and the decomposition into even (bosonic) and odd (fermionic) subspaces.
* **Anticommutation & Polarization:** Verifying orthogonal anticommutation relations, bivector Lie brackets ($\mathfrak{so}(M, Q)$), and multiplicative properties of the Clifford norm.
* **Future Directions:** Constructing $\mathrm{Pin}$ and $\mathrm{Spin}$ groups as subgroups of units, exploring double covers, and formalizing simple spinor representations (Dirac/Weyl).

---

## Repository Structure

```text
lean4phys/
├── Lean4phys/          # Main formalization library and developed proofs
├── tutoriale_puste/    # Problem sets, exercise templates, and self-study modules
├── Lean4phys.lean      # Top-level module import
├── lakefile.toml       # Lake package configuration and Mathlib dependencies
└── lean-toolchain      # Active Lean 4 compiler version pin

```

---

## Getting Started

### Prerequisites

Ensure you have `elan` (the Lean version manager) installed. Follow the instructions at [leanprover-community.github.io](https://leanprover-community.github.io/get_started.html) if needed.

### Building Locally

Clone the repository and fetch the precompiled Mathlib cache:

```bash
git clone [https://github.com/boroboro1/lean4phys.git](https://github.com/boroboro1/lean4phys.git)
cd lean4phys

# Download precompiled olean binaries for Mathlib
lake exe cache get

# Build the project
lake build

```

### Editor Setup

We recommend using **VS Code** with the official **Lean 4** extension (`leanprover.lean4`). Open the repository root directory directly (`code .`) so Lake automatically resolves environment paths and the interactive InfoView.

---

## References

* Lean Prover Community, *Mathematics in Lean* & *Mathlib Documentation*.
* H. Blaine Lawson & Marie-Louise Michelsohn, *Spin Geometry*, Princeton University Press (1989).
* Pertti Lounesto, *Clifford Algebras and Spinors*, Cambridge University Press (2001).


