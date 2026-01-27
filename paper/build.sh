#!/bin/bash
# Build script for the Computational Paths paper

cd "$(dirname "$0")"

# Run pdflatex and bibtex
pdflatex -interaction=nonstopmode paper.tex
bibtex paper
pdflatex -interaction=nonstopmode paper.tex
pdflatex -interaction=nonstopmode paper.tex

echo "Build complete. Output: paper.pdf"
