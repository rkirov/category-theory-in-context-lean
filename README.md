# Lean Companion to Riehl's Category Theory in Context

This repo is a Lean companion to the Category Theory in Context textbook. The book is
freely available https://emilyriehl.github.io/files/context.pdf.

In this branch all problems have solutions.

## Current progress

- Chapter 1 - Sections 1, 2, 3, 4

## How to write a Lean companion to an existing math textbook

This is inspired by Tao's https://github.com/teorth/analysis companion.

The rough plan for writing a Lean companion is:

- each chapter gets its own .lean file
- each definition, theorem and example from the text are writen to follow the style of the text as much as possible.
- each exercise is writen as a theorem statement with a `sorry` for the proof.
- in the chapters that introduce a new concept it is written in the .lean file and not imported from mathlib (even if it exists there)
- in subsequent chapters, the mathlib definition can be used (hopefully it is equivalent, but with better usability, say custom tactics etc)

## Contributing

This is very much work in progress and an experiement. I am not an expert in Lean or category theory, so unclear to me:

- which proofs and exercises from the text are amenable to formalization
- how well can Lean support the concepts in the book
- the pedagogical approach from the book can be followed without accidentally picking up too much complexity for some Lean technical reason.

PRs are very welcome.
