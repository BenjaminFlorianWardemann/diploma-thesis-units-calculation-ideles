# Zur Einheitenberechnung mittels Idelen

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18519141.svg)](https://doi.org/10.5281/zenodo.18519141)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

This repository contains the Magma implementation accompanying the Diplomarbeit „Zur Einheitenberechnung mittels Idelen” (TU Berlin, 2011, advisor M. Pohst). It computes maximal systems of independent S-units in global fields, i.e. number fields and function fields, uniformly, by a generalized Lagrange algorithm walking through S-minima. Adeles and ideles are implemented as explicit finite data structures with verified arithmetic (adeles.m), at a time when they were generally considered a purely theoretical tool avoided in concrete computation; the first widely known computational treatment, M. Hertogh’s Computing with adèles and idèles (Leiden, 2021) and its SageMath package, appeared a decade later. Unit independence is certified via Fieker–Pohst precision bounds.
