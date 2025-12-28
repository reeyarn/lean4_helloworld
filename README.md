# lean4_helloworld

A simple repository documenting my journey learning Lean 4, a theorem prover and functional programming language. This repo contains basic examples, starting from installation instructions to my first simple mathematical proofs in Lean 4.

## About Lean 4

Lean 4 is an open-source theorem prover and programming language developed by Microsoft Research. It allows you to write formally verified mathematical proofs and correct-by-construction programs.

This repository shares my personal approach to getting started with Lean 4 and experimenting with simple proofs.

## Getting Started: Installing Lean 4

The easiest and recommended way to use Lean 4 is with **Visual Studio Code (VS Code)** and the official Lean 4 extension
[`vscode:extension/leanprover.lean4`](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

For more details, see the official guide: [https://lean-lang.org/install/](https://lean-lang.org/install/).

## Creating Your First Lean Project

Once Lean is installed:

1. Open a folder in VS Code (this will be your project).
2. Create a new Lean package:
   - Open the terminal in VS Code (`Ctrl+``).
   - Run:  
     ```bash
     lake +leanprover/lean4:latest new my_project
     ``` 