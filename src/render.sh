#!/bin/bash
rm -f html/*.md html/*.html
agda --html --html-highlight=auto --css=Agda.css index.lagda.md
for f in html/*.md; do pandoc $f -o ${f%.md}.html -s --css=Agda.css; done
