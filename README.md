# lean4_helloworld

A simple repository documenting my journey learning Lean 4, a theorem prover and functional programming language. This repo contains basic examples, starting from installation instructions to my first simple mathematical proofs in Lean 4.

## About Lean 4

Lean 4 is an open-source theorem prover and programming language developed by Microsoft Research. It allows you to write formally verified mathematical proofs and correct-by-construction programs.

This repository shares my personal approach to getting started with Lean 4 and experimenting with simple proofs.

## Getting Started: Installing Lean 4

The easiest and recommended way to use Lean 4 is with **Visual Studio Code (VS Code)** and the official Lean 4 extension.

1. **Install VS Code**  
   Download and install from [https://code.visualstudio.com/](https://code.visualstudio.com/).

2. **Install the Lean 4 extension**  
   - Open VS Code.
   - Go to the Extensions view (`Ctrl+Shift+X` or `Cmd+Shift+X` on macOS).
   - Search for "lean4".
   - Install the extension published by **Lean FRO** (official).

3. **Complete the setup**  
   - After installing the extension, create a new file and save it with a `.lean` extension (e.g., `Hello.lean`).
   - Or open a new empty file and change the language mode to "Lean 4" (bottom-right corner).
   - The extension will prompt you to install Lean using **elan** (the Lean version manager). Follow the instructions—it will download and set up everything automatically.
   - A "Welcome" or setup guide page should appear with step-by-step help.

For more details, see the official guide: [https://lean-lang.org/lean4/](https://lean-lang.org/lean4/).

## Creating Your First Lean Project

Once Lean is installed:

1. Open a folder in VS Code (this will be your project).
2. Create a new Lean package:
   - Open the terminal in VS Code (`Ctrl+``).
   - Run:  
     ```bash
     lake +leanprover/lean4:latest new my_project
